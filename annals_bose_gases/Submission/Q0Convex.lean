import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Q0Ren
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — Q0-convexity in the condensed count (S6-3 step 1)

Chosen-branch instantiation of the condensed-count algebra of
`Submission.CondensedAlg` with the Q0-renormalized value of
`Submission.Q0Ren`.  For a *normalized* continuous state `Φ` over
`abox N ℓ`, `0 ≤ μ`, in the chosen scattering branch
(`h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`, kernels `wPairU ℓ (g2 v h)`
and `wPairU ℓ (g0 v h)` as in `q0_chosen_lower`), we get the *Q0 convexity /
concentration handle*:

    E(Φ) := ½Σ_{i≠j}∫(PᵢPⱼΦ)²·wPairU(g2) − μΣᵢ∫(PᵢΦ)²·(∫wPairU(g0))
    E(Φ) ≥ (4πa/ℓ³)(S₁²−S₁) − 8πaμS₁                            (q0_chosen_sq_lower)
    E(Φ) ≥ (4πa/ℓ³)(S₁−μℓ³−½)² − 4πaμ²ℓ³(1+1/(2μℓ³))²          (q0_concentration)

Here `S₁ = cS1 ℓ Φ`, `a = a v`, and the second inequality is the exact
completion of the square (`CondensedAlg.q0_square_identity`); it is the
algebraic mechanism that (once combined with an upper energy threshold from
the later Bogoliubov/3Q layers) forces the condensed count `S₁` close to
`μℓ³` and yields the leading `−4πaμ²ℓ³` term of the LHY box bound.

## Route notes (for the child)

* `q0_chosen_sq_lower`: `q0_chosen_lower` (`Q0Ren`) gives
  `(1/2)(ℓ³)⁻¹(8πa)S₂ − 8πaμS₁ ≤ E(Φ)`.  Since `(1/2)(ℓ³)⁻¹(8πa) = 4πa/ℓ³`
  and `S₂ ≥ S₁²−S₁` (`CondensedAlg.cS2_ge_sq_sub`, needs `hnorm`), multiply
  by the nonnegative coefficient `0 ≤ 4πa/ℓ³` (use `0 ≤ a v` from
  `ScatT3.chosen_av_bounds_weak hR hv_nonneg hvrad hv_supp h` and `0 < ℓ`)
  and combine with `nlinarith`.  (No `hμ` needed here.)
* `q0_concentration`: apply `q0_square_identity` (`CondensedAlg`) with
  `S := cS1 ℓ Φ`, `a := a v`, `l := ℓ`, `μ := μ` — needs `ℓ ≠ 0` (from
  `hℓ`) and `μ ≠ 0` (from `hμ`) — and chain with `q0_chosen_sq_lower`
  (rewrite `8πaμS₁` ↔ `(8πa)·μ·cS1` by `ring`).  The final RHS must match
  exactly the square form; `nlinarith`/`ring_nf` will close.

Hypotheses block (mirrors `Q0Ren` + normalization):
`(hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
(hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
(h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
(hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (μ : ℝ) (hΦc : Continuous Φ)
(hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)`, plus `(hμ : 0 < μ)` only for
`q0_concentration`.

`E(Φ)` is spelled out inline (matching `q0_chosen_lower`'s LHS exactly);
the count is `cS1`/`cS2` (`CentredSector`), pairs `pairSet N` (`Q0Value`),
projections `aP` (`Q0Sector`), kernels `g0 v h`, `g2 v h` and `wPairU`
(`ScatKernelChosen`/`Q0Chosen`).  The chosen branch supplies
`0 ≤ a v` via `ScatT3.chosen_av_bounds_weak`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Self-contained condensed-count concentration machinery

The statements below re-derive (in this file, with fresh names) the two
facts of the condensed-count algebra that the two main lemmas need:
the **completion-of-the-square** identity (`q0c_square_identity`, pure real
algebra) and the **condensed-number concentration** bound
`S₂ ≥ S₁² − S₁` (`cS2_ge_sq_sub_self`, Cauchy--Schwarz over the analysis
box).  They are kept local so that `q0_chosen_sq_lower` / `q0_concentration`
do not depend on the (possibly still in progress) algebra module
`Submission.CondensedAlg`; all ingredients come from the already-proven
`CentredSector`/`Q0Sector`/`Q0Value`/`Q0Ren` layers.
-/

/-- Completion of the square (exact real algebra, needs `l ≠ 0`, `μ ≠ 0`):
`(4πa/l³)(S²−S) − (8πa)μS = (4πa/l³)(S − μl³ − ½)² − 4πaμ²l³(1+1/(2μl³))²`. -/
lemma q0c_square_identity (a μ l S : ℝ) (hl : l ≠ 0) (hμ : μ ≠ 0) :
    (4 * π * a / l ^ 3) * (S ^ 2 - S) - (8 * π * a) * μ * S =
      (4 * π * a / l ^ 3) * (S - μ * l ^ 3 - (1 / 2 : ℝ)) ^ 2
        - (4 * π * a) * μ ^ 2 * l ^ 3 * (1 + 1 / (2 * μ * l ^ 3)) ^ 2 := by
  field_simp [hl, hμ]
  ring

/-- Bilinear Cauchy--Schwarz over the centred box:
`(∫ f·g)² ≤ (∫f²)(∫g²)` for continuous `f g`. -/
lemma cs_box_product {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : X N → ℝ}
    (hfc : Continuous f) (hgc : Continuous g) :
    (∫ x in abox N ℓ, f x * g x) ^ 2 ≤
      (∫ x in abox N ℓ, (f x) ^ 2) * (∫ x in abox N ℓ, (g x) ^ 2) := by
  let μ' : Measure (X N) := (volume : Measure (X N)).restrict (abox N ℓ)
  have hfin : IsFiniteMeasure μ' := by
    refine ⟨?set⟩
    rw [Measure.restrict_apply_univ]
    exact abox_lt_top N ℓ hℓ.le
  letI : IsFiniteMeasure μ' := hfin
  obtain ⟨Cf, hCf⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := f)
    hfc.continuousOn
  obtain ⟨Cg, hCg⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := g)
    hgc.continuousOn
  have hbf : ∀ᵐ x ∂μ', |f x| ≤ Cf := by
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    exact ae_of_all volume (fun x hx => by simpa [Real.norm_eq_abs] using hCf x hx)
  have hbg : ∀ᵐ x ∂μ', |g x| ≤ Cg := by
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    exact ae_of_all volume (fun x hx => by simpa [Real.norm_eq_abs] using hCg x hx)
  have hmf : AEStronglyMeasurable f μ' := hfc.aestronglyMeasurable
  have hmg : AEStronglyMeasurable g μ' := hgc.aestronglyMeasurable
  have hmemf : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ' :=
    MemLp.of_bound hmf.norm Cf (by filter_upwards [hbf] with x hx; simpa using hx)
  have hmemg : MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ' :=
    MemLp.of_bound hmg.norm Cg (by filter_upwards [hbg] with x hx; simpa using hx)
  have hnonf : 0 ≤ᵐ[μ'] (fun x => |f x|) := ae_of_all _ (fun _ => abs_nonneg _)
  have hnong : 0 ≤ᵐ[μ'] (fun x => |g x|) := ae_of_all _ (fun _ => abs_nonneg _)
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := μ')
    Real.HolderConjugate.two_two hnonf hnong hmemf hmemg
  have hc1 : (∫ x, |f x| * |g x| ∂μ') = ∫ x, |f x * g x| ∂μ' := by
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_mul]
  have hsqf : (fun x => |f x| ^ (2 : ℝ)) = fun x => (f x) ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  have hsqg : (fun x => |g x| ^ (2 : ℝ)) = fun x => (g x) ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  have hA0 : 0 ≤ ∫ x, (f x) ^ 2 ∂μ' := integral_nonneg (fun _ => sq_nonneg _)
  have hB0 : 0 ≤ ∫ x, (g x) ^ 2 ∂μ' := integral_nonneg (fun _ => sq_nonneg _)
  have hR : (∫ x, |f x * g x| ∂μ')
      ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ') := by
    rw [hc1, hsqf, hsqg] at hmain
    simpa [Real.sqrt_eq_rpow] using hmain
  have habs : |∫ x, f x * g x ∂μ'| ≤ ∫ x, |f x * g x| ∂μ' :=
    abs_integral_le_integral_abs (μ := μ') (f := fun x => f x * g x)
  have hsq1 : (∫ x, |f x * g x| ∂μ') ^ 2
      ≤ (∫ x, (f x) ^ 2 ∂μ') * (∫ x, (g x) ^ 2 ∂μ') := by
    have h1 : |∫ x, |f x * g x| ∂μ'| ≤
        |Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ')| := by
      calc
        |∫ x, |f x * g x| ∂μ'| = ∫ x, |f x * g x| ∂μ' :=
          abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))
        _ ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ') := hR
        _ = |Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ')| :=
          (abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    calc
      (∫ x, |f x * g x| ∂μ') ^ 2
          ≤ (Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ')) ^ 2 := sq_le_sq.mpr h1
      _ = (∫ x, (f x) ^ 2 ∂μ') * (∫ x, (g x) ^ 2 ∂μ') := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hsq2 : (∫ x, f x * g x ∂μ') ^ 2 ≤ (∫ x, |f x * g x| ∂μ') ^ 2 := by
    have hnn : 0 ≤ ∫ x, |f x * g x| ∂μ' := integral_nonneg (fun _ => abs_nonneg _)
    have h1 : |∫ x, f x * g x ∂μ'| ≤ |∫ x, |f x * g x| ∂μ'| := by
      calc
        |∫ x, f x * g x ∂μ'| ≤ ∫ x, |f x * g x| ∂μ' := habs
        _ = |∫ x, |f x * g x| ∂μ'| := (abs_of_nonneg hnn).symm
    exact sq_le_sq.mpr h1
  calc
    (∫ x in abox N ℓ, f x * g x) ^ 2
        = (∫ x, f x * g x ∂μ') ^ 2 := by rfl
    _ ≤ (∫ x, |f x * g x| ∂μ') ^ 2 := hsq2
    _ ≤ (∫ x, (f x) ^ 2 ∂μ') * (∫ x, (g x) ^ 2 ∂μ') := hsq1
    _ = (∫ x in abox N ℓ, (f x) ^ 2) * (∫ x in abox N ℓ, (g x) ^ 2) := by rfl

/-- Self-adjointness + idempotence of `Pᵢ` over the box:
`∫Φ·(PᵢΦ) = ∫(PᵢΦ)²`. -/
lemma aP_selfadj_int {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, Φ x * aP ℓ i Φ x) = ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 := by
  have hcontP : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
  have hsym := aP_sym_box hℓ i (Φ := aP ℓ i Φ) (Ψ := Φ) hcontP hΦc
  calc
    (∫ x in abox N ℓ, Φ x * aP ℓ i Φ x)
        = ∫ x in abox N ℓ, aP ℓ i Φ x * Φ x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [mul_comm]
    _ = ∫ x in abox N ℓ, aP ℓ i (aP ℓ i Φ) x * Φ x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [← aP_idem hℓ i hΦc x]
    _ = ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aP ℓ i Φ x) := hsym
    _ = ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with x
          rw [← pow_two]

/-- `S₁ = ∫ Φ·(Σᵢ PᵢΦ)`: `cS1` is the overlap of `Φ` with the pointwise
condensed sum. -/
lemma cS1_eq_overlap {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    cS1 ℓ Φ = ∫ x in abox N ℓ, Φ x * (∑ i : Fin N, aP ℓ i Φ x) := by
  unfold cS1
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
        = ∑ i : Fin N, ∫ x in abox N ℓ, Φ x * aP ℓ i Φ x := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [aP_selfadj_int hℓ i hΦc]
    _ = ∫ x in abox N ℓ, (∑ i : Fin N, Φ x * aP ℓ i Φ x) := by
          rw [integral_finsetSum (s := Finset.univ) (f := fun i : Fin N => fun x : X N => Φ x * aP ℓ i Φ x)
            (μ := (volume : Measure (X N)).restrict (abox N ℓ))]
          intro i hi
          exact integrableOn_mul_aP hℓ i hΦc hΦc
    _ = ∫ x in abox N ℓ, Φ x * (∑ i : Fin N, aP ℓ i Φ x) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [Finset.mul_sum]

/-- `‖PᵢPⱼΦ‖² = ⟨PᵢΦ, PⱼΦ⟩` over the box (self-adjointness and
idempotence/commutation of the projections). -/
lemma aP_pair_mixed {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2) =
      ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aP ℓ j Φ x) := by
  have hcontP : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
  have hcontiP : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i hcontP
  have hs1 := aP_sym_box hℓ i (Φ := aP ℓ j Φ) (Ψ := aP ℓ i (aP ℓ j Φ)) hcontP hcontiP
  have hs2 := aP_sym_box hℓ j (Φ := Φ) (Ψ := aP ℓ i (aP ℓ j Φ)) hΦc hcontiP
  have hs3 := aP_sym_box hℓ i (Φ := Φ) (Ψ := aP ℓ j Φ) hΦc hcontP
  have hpt : ∀ x, Φ x * (aP ℓ i (aP ℓ j (aP ℓ j Φ)) x) = Φ x * (aP ℓ i (aP ℓ j Φ) x) := by
    intro x
    have harg : (aP ℓ i (aP ℓ j (aP ℓ j Φ))) x = (aP ℓ i (aP ℓ j Φ)) x :=
      congrArg (fun w : X N → ℝ => aP ℓ i w x) (funext (fun y => aP_idem hℓ j hΦc y))
    rw [harg]
  calc
    (∫ x in abox N ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2)
        = ∫ x in abox N ℓ, (aP ℓ i (aP ℓ j Φ) x) * (aP ℓ i (aP ℓ j Φ) x) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [← pow_two]
    _ = ∫ x in abox N ℓ, (aP ℓ j Φ x) * (aP ℓ i (aP ℓ i (aP ℓ j Φ)) x) := hs1
    _ = ∫ x in abox N ℓ, (aP ℓ j Φ x) * (aP ℓ i (aP ℓ j Φ) x) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [aP_idem hℓ i hcontP x]
    _ = ∫ x in abox N ℓ, Φ x * (aP ℓ j (aP ℓ i (aP ℓ j Φ)) x) := hs2
    _ = ∫ x in abox N ℓ, Φ x * (aP ℓ i (aP ℓ j (aP ℓ j Φ)) x) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [aP_comm hℓ j i hcontP x]
    _ = ∫ x in abox N ℓ, Φ x * (aP ℓ i (aP ℓ j Φ) x) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpt x
    _ = ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aP ℓ j Φ x) := hs3.symm

/-- `S₂ = Σ_{i≠j} ∫(PᵢΦ)(PⱼΦ)`: rewrite each `‖PᵢPⱼΦ‖²` summand of `cS2`
through `aP_pair_mixed`. -/
lemma cS2_eq_pair_mixed {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    cS2 ℓ Φ = ∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x) := by
  unfold cS2
  apply Finset.sum_congr rfl
  intro p hp
  exact aP_pair_mixed hℓ p.1 p.2 hΦc

/-- The diagonal (`p.1 = p.2`) part of the pair sum equals `S₁`. -/
lemma diagonal_sum_eq_cS1 {N : ℕ} {ℓ : ℝ} (_hℓ : 0 < ℓ) {Φ : X N → ℝ} (_hΦc : Continuous Φ) :
    (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p : Fin N × Fin N => ¬ p.1 ≠ p.2),
        ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x)) = cS1 ℓ Φ := by
  unfold cS1
  refine Finset.sum_bij
    (s := (Finset.univ : Finset (Fin N × Fin N)).filter (fun p : Fin N × Fin N => ¬ p.1 ≠ p.2))
    (t := (Finset.univ : Finset (Fin N)))
    (f := fun p : Fin N × Fin N => ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x))
    (g := fun i : Fin N => ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
    (i := fun p hp => p.1) ?_ ?_ ?_ ?_
  · intro p hp
    simp
  · intro p₁ hp₁ p₂ hp₂ h
    apply Prod.ext
    · exact h
    · have hp1 : p₁.1 = p₁.2 := by
        have hnp : ¬ p₁.1 ≠ p₁.2 := (Finset.mem_filter.mp hp₁).2
        by_contra hc
        exact hnp hc
      have hp2 : p₂.1 = p₂.2 := by
        have hnp : ¬ p₂.1 ≠ p₂.2 := (Finset.mem_filter.mp hp₂).2
        by_contra hc
        exact hnp hc
      rw [← hp1, ← hp2]
      exact h
  · intro b hb
    refine ⟨(b, b), ?_, rfl⟩
    simp
  · intro p hp
    have hp_eq : p.1 = p.2 := by
      have hnp : ¬ p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      by_contra hc
      exact hnp hc
    calc
      (∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x))
          = ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.1 Φ x) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hp_eq]
      _ = ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) ^ 2 := by
            apply integral_congr_ae
            filter_upwards with x
            rw [← pow_two]

/-- `∫(Σᵢ PᵢΦ)² = S₁ + S₂`: expand the square over ordered pairs, split
into diagonal (`= S₁`) and off-diagonal (`= S₂`). -/
lemma sq_n0_eq_add_self {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    ∫ x in abox N ℓ, (∑ i : Fin N, aP ℓ i Φ x) ^ 2 = cS1 ℓ Φ + cS2 ℓ Φ := by
  have hA : (∫ x in abox N ℓ, (∑ i : Fin N, aP ℓ i Φ x) ^ 2)
      = ∑ p : Fin N × Fin N, ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x) := by
    calc
      (∫ x in abox N ℓ, (∑ i : Fin N, aP ℓ i Φ x) ^ 2)
          = ∫ x in abox N ℓ, ∑ p : Fin N × Fin N, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [pow_two, Finset.sum_mul_sum]
            rw [← Finset.sum_product (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin N))
              (fun p : Fin N × Fin N => (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x))]
            rw [Finset.univ_product_univ]
      _ = ∑ p : Fin N × Fin N, ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x) := by
            rw [integral_finsetSum (s := Finset.univ)
              (f := fun p : Fin N × Fin N => fun x : X N => (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x))
              (μ := (volume : Measure (X N)).restrict (abox N ℓ))]
            intro p hp
            exact integrableOn_abox_of_continuous hℓ
              ((aP_continuous hℓ p.1 hΦc).mul (aP_continuous hℓ p.2 hΦc))
  have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Fin N × Fin N)))
      (p := fun p : Fin N × Fin N => p.1 ≠ p.2)
      (f := fun p : Fin N × Fin N => ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x))
  have hdiag : (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p : Fin N × Fin N => ¬ p.1 ≠ p.2),
      ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x)) = cS1 ℓ Φ :=
    diagonal_sum_eq_cS1 hℓ hΦc
  have hoff : (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p : Fin N × Fin N => p.1 ≠ p.2),
      ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x)) = cS2 ℓ Φ := by
    simpa [pairSet] using (cS2_eq_pair_mixed hℓ hΦc).symm
  calc
    (∫ x in abox N ℓ, (∑ i : Fin N, aP ℓ i Φ x) ^ 2)
        = ∑ p : Fin N × Fin N, ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x) := hA
    _ = (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p : Fin N × Fin N => p.1 ≠ p.2),
            ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x))
        + (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p : Fin N × Fin N => ¬ p.1 ≠ p.2),
            ∫ x in abox N ℓ, (aP ℓ p.1 Φ x) * (aP ℓ p.2 Φ x)) := by
          rw [hsplit]
    _ = cS2 ℓ Φ + cS1 ℓ Φ := by rw [hoff, hdiag]
    _ = cS1 ℓ Φ + cS2 ℓ Φ := by ring

/-- Condensed-number concentration (Cauchy–Schwarz on the box): for a
normalized `Φ`, `S₂ ≥ S₁² − S₁`. -/
lemma cS2_ge_sq_sub_self {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    cS1 ℓ Φ * cS1 ℓ Φ - cS1 ℓ Φ ≤ cS2 ℓ Φ := by
  let g : X N → ℝ := fun x => ∑ i : Fin N, aP ℓ i Φ x
  have hgc : Continuous g := by
    unfold g
    exact continuous_finsetSum (Finset.univ) (fun i hi => aP_continuous hℓ i hΦc)
  have hCS := cs_box_product hℓ hΦc hgc
  have hov : cS1 ℓ Φ = ∫ x in abox N ℓ, Φ x * g x := by
    unfold g
    exact cS1_eq_overlap hℓ hΦc
  have hsq : (∫ x in abox N ℓ, (g x) ^ 2) = cS1 ℓ Φ + cS2 ℓ Φ := by
    unfold g
    exact sq_n0_eq_add_self hℓ hΦc
  have h1 : (∫ x in abox N ℓ, Φ x * g x) ^ 2 ≤ ∫ x in abox N ℓ, (g x) ^ 2 := by
    calc
      (∫ x in abox N ℓ, Φ x * g x) ^ 2
          ≤ (∫ x in abox N ℓ, (Φ x) ^ 2) * (∫ x in abox N ℓ, (g x) ^ 2) := hCS
      _ = ∫ x in abox N ℓ, (g x) ^ 2 := by rw [hnorm]; ring
  have h2 : cS1 ℓ Φ * cS1 ℓ Φ ≤ cS1 ℓ Φ + cS2 ℓ Φ := by
    rw [← hov] at h1
    rw [hsq] at h1
    simpa [pow_two] using h1
  nlinarith

/-- Q0 convexity in the condensed count, without completing the square:
`E(Φ) ≥ (4πa/ℓ³)(S₁²−S₁) − 8πaμS₁` for normalized `Φ`, where `E(Φ)` is the
chosen-branch Q0 expectation (`½Σ∫(PᵢPⱼΦ)²w₂ − μΣ∫(PᵢΦ)²∫w₁`). -/
lemma q0_chosen_sq_lower {N : ℕ} {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (μ : ℝ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    (4 * π * a v / ℓ ^ 3) * (cS1 ℓ Φ * cS1 ℓ Φ - cS1 ℓ Φ)
        - (8 * π * a v) * μ * cS1 ℓ Φ
      ≤ (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y))) := by
  have hL := q0_chosen_lower hR hv_nonneg hvrad hv_supp h hℓ hRℓ μ hΦc
  have hCS := cS2_ge_sq_sub_self hℓ hΦc hnorm
  have ha : 0 ≤ a v := (chosen_av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hnum : 0 ≤ 4 * π * a v := by positivity
  have hcoef : 0 ≤ 4 * π * a v / ℓ ^ 3 := div_nonneg hnum (pow_nonneg hℓ.le 3)
  have hmul : (4 * π * a v / ℓ ^ 3) * (cS1 ℓ Φ * cS1 ℓ Φ - cS1 ℓ Φ)
      ≤ (4 * π * a v / ℓ ^ 3) * cS2 ℓ Φ :=
    mul_le_mul_of_nonneg_left hCS hcoef
  have hident : (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (8 * π * a v) = 4 * π * a v / ℓ ^ 3 := by
    field_simp [ne_of_gt hℓ]
    ring
  calc
    (4 * π * a v / ℓ ^ 3) * (cS1 ℓ Φ * cS1 ℓ Φ - cS1 ℓ Φ)
        - (8 * π * a v) * μ * cS1 ℓ Φ
        ≤ (4 * π * a v / ℓ ^ 3) * cS2 ℓ Φ - (8 * π * a v) * μ * cS1 ℓ Φ := by
          nlinarith [hmul]
    _ = (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v) * cS2 ℓ Φ - (8 * π * a v) * μ * cS1 ℓ Φ := by
          rw [hident]
    _ ≤ (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y))) := hL

/-- Q0 concentration (completion of the square): for normalized `Φ` and
`0 < μ`, `E(Φ) ≥ (4πa/ℓ³)(S₁−μℓ³−½)² − 4πaμ²ℓ³(1+1/(2μℓ³))²`. -/
lemma q0_concentration {N : ℕ} {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (μ : ℝ) (hμ : 0 < μ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    (4 * π * a v / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2
        - (4 * π * a v) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
      ≤ (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y))) := by
  have hSq := q0_chosen_sq_lower hR hv_nonneg hvrad hv_supp h hℓ hRℓ μ hΦc hnorm
  have hid := q0c_square_identity (a v) μ ℓ (cS1 ℓ Φ) (ne_of_gt hℓ) (ne_of_gt hμ)
  rw [← pow_two (cS1 ℓ Φ)] at hSq
  rw [hid] at hSq
  exact hSq

end BoseGases

end Submission
