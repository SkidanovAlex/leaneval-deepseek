import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Q3Q4Peel
import Submission.Work.SmallBoxQ0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Option (b) — the √-factorisation arithmetic core (Session-155)

Record of the Session-154 verdict and its (b)-resolution, in machine-checked
form.  Session-154 pinned the √-factorisation CS (option (b)) as FORCED:
the coefficient-1 AM–GM (`q1_cross_w1_cs`) leaves the `u`-quadratic CONCAVE
(`q0RenVal − (u−μ)²·8πa·S ≈ 8πaV[½u²−μu−u(u−μ)²] ~ −8πaV·u³` for `u ≫ μ`,
with `S ≈ uV`), unusable for the FS group trick; only a Q-part-LINEAR /
P-part-CONVEX split can be gap-absorbed while keeping FS's `¼`-coefficient.

Session-155 closes the arithmetic core of option (b) — with NO √-algebra:
the free-ε AM–GM at `ε := V/(4S)` (`V := ℓ³`, `S := cS1`) is the pure-real
identity `(V·t·P + 4S·Q)² ≥ 0` divided by `4SV > 0`, giving the FS-shape CS

    q1_cross_w1_cs_fs :  2t·OB₁ ≥ −¼·t²·8πa·V − (4S/V)·qOneMass

(machine-checked, Q3Q4Peel decl #60: per-slot `0 ≤ ∫(VtP+4SQ)²f₁`, expand,
`Σ∫P²f₁ = 8πaS`, `Σ∫Q²f₁ = qOneMass`, factor out `4SV`, divide).  Feeding it
into the `pot_sharp_w1line` chain at `t := u−μ` yields the scoped (b)-bound

    pot_sharp_w1line_cs_fs :
      qLHS ≥ q0RenVal − ¼·(u−μ)²·8πa·V − (4S/V)·qOneMass − 2·(ℓ³)⁻¹·Corr − masses

(Q3Q4Peel decl #61, machine-checked: the `pot_sharp_w1line_cs` assembly with
the FS-shape CS in place of the coefficient-1 CS; needs `0 < cS1`).

The concavity obstruction is thereby RESOLVED — the machine-checked identity
`q0_convex_plus_fs_Ppart` below shows that (at `S := uV`, the dummy-regime
scale) the q0-convex part PLUS the new P-part equals FS's convex remainder
main term exactly:

    ½V⁻¹·8πa·((uV)²−uV) − 8πa·μ·uV − ¼(u−μ)²·8πa·V
      = ¼(u−μ)²·8πa·V − ½μ²·8πa·V − 4πa·u        (u²-coefficient ¼·8πaV > 0)

i.e. the `u³`-concavity (`q0_concave_diagnostic_old_cs`, the old
coefficient-1 combination, kept as the Session-153 record) is replaced by a
CONVEX `¼(u−μ)²·8πaV`-quadratic minus the harmless LINEAR `−4πa·u`.  The
Q-part `(4S/V)·qOneMass` is LINEAR in the Q²-masses (coefficient `4S/V = 4u`
at `S = uV`); its gap absorption is the documented next step (route:
`QMassUpper.qOneMass ≤ (8πa)·q2MassChi + Err·cnPlus` machinery consumed by
the q2-side `−μ·qOneMass`-lower bounds, exactly as the corpus's
`qLHS_sharp_u`/`gap_absorb_sharp` family absorbs its `n₊`-blocks).

Machine-checked content below: (1) `pot_sharp_w1line_cs_fs_repulsion` — the
(b)-bound in scoped form with q0's CONVEX repulsion form exposed (the
statement the final windowed/gap step consumes); (2)
`fs_square_factorisation` — the pure-real factorisation identity at the heart
of `q1_cross_w1_cs_fs`; (3) `q0_convex_plus_fs_Ppart` — the convexity
identity (the arithmetic check the Session-154 verdict demanded, in the
dummy regime `S := uV`, general `a, μ`); (4) `q0_concave_diagnostic_old_cs`
— the old concave combination (record); (5) the typeset
`step4_sqrt_target_statement` — the per-state target with `kinWord` on the
left, whose `u`-quadratic is the CONVEX `¼`-form.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The scoped (b)-bound with q0's repulsion form exposed** (all-Φ): from
`pot_sharp_w1line_cs_fs` (`qLHS ≥ q0RenVal − ¼(u−μ)²·8πa·V −
(4S/V)·qOneMass − 2·(ℓ³)⁻¹·Corr − masses`) and `q0RenVal_repulsion`
(`q0RenVal ≥ (4πa/V)(S−μV−½)² − 4πaμ²V(1+1/(2μV))²`, needs `0<μ`, `∫Φ²=1`):

    qLHS ≥ (4πa/V)(cS1−μV−½)² − 4πaμ²V(1+1/(2μV))²
           − ¼(u−μ)²·8πa·V − (4·cS1/V)·qOneMass − 2V⁻¹·Corr − masses .

The `u`-quadratic of the first two lines is CONVEX with FS `¼`-coefficient
(`q0_convex_plus_fs_Ppart`); the third line is LINEAR in the Q²-masses and is
what the kinetic gap must absorb (next step, via the `QMassUpper` q2-side).
`masses` is the `pot_sharp_w1line` tail (fsqC2/fsqC1/μ-blocks). -/
lemma pot_sharp_w1line_cs_fs_repulsion {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hSc1 : 0 < cS1 ℓ Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2
      - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
      - (1 / 4) * ((((N : ℝ) / ℓ ^ 3) - μ) ^ 2) * ((8 * π * (a v)) * ℓ ^ 3)
      - ((4 * (cS1 ℓ Φ)) / ℓ ^ 3) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
      - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
            (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ := by
  have hcs := pot_sharp_w1line_cs_fs hℓ hμ.le hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hSc1
  have hrep := q0RenVal_repulsion hR hv_nonneg hvrad hv_supp h hℓ hRℓ hμ hΦc hnorm
  -- hcs : qLHS ≥ q0RenVal − ¼(u−μ)²8πaV − (4S/V)qOneMass − 2V⁻¹Corr − masses
  -- hrep : (4πa/V)(S−μV−½)² − 4πaμ²V(1+1/(2μV))² ≤ q0RenVal
  nlinarith

/-- **Pure-real factorisation at the heart of `q1_cross_w1_cs_fs`**: the
per-slot-square sum `0 ≤ V²t²·(8πa·S) + 8VSt·c + 16S²·q` is exactly
`4SV · [¼t²·(8πa·V) + 2t·c + (4S/V)·q]`, so dividing by `4SV > 0`
(`nonneg_of_mul_nonneg_left`) gives the FS-shape CS — no √ needed.  Here `k`
is the coupling `8πa`, `c` the cross sum `OB₁`, `q` the mass `qOneMass`. -/
lemma fs_square_factorisation (V S t c q k : ℝ) (hV : V ≠ 0) :
    (V ^ 2 * t ^ 2) * (k * S) + (8 * V * S * t) * c + (16 * S ^ 2) * q
      = ((4 * S) * V) * ((1 / 4) * t ^ 2 * (k * V) + 2 * t * c + ((4 * S) / V) * q) := by
  field_simp [hV]
  ring

/-- **The convexity check (option (b), dummy regime `S := u·V`, general
`a, μ`)**: the q0-convex part (with `cS2 → S²−S` at `S := uV`) PLUS the new
FS-shape P-part `−¼(u−μ)²·8πa·V` equals FS's convex remainder main term
`¼(u−μ)²·8πaV − ½μ²·8πaV` minus the harmless LINEAR `−4πa·u`.  The
`u²`-coefficient is `¼·8πa·V > 0` — CONVEX (the `u³`-concavity is gone).
This is the machine-checked arithmetic behind the Session-154 verdict's
"(μ=a=1: P-part becomes −¼(u−μ)²8πaV, convex FS form restored)". -/
lemma q0_convex_plus_fs_Ppart (a μ V u : ℝ) (hV : V ≠ 0) :
    (1 / 2 : ℝ) * V⁻¹ * (8 * π * a) * ((u * V) ^ 2 - u * V)
      - (8 * π * a) * μ * (u * V)
      - (1 / 4 : ℝ) * (u - μ) ^ 2 * (8 * π * a * V)
    = (1 / 4 : ℝ) * (u - μ) ^ 2 * (8 * π * a * V)
      - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * a * V)
      - 4 * π * a * u := by
  field_simp [hV]
  ring

/-- **Record of the Session-153 obstruction (old coefficient-1 CS)**: with
the coefficient-1 P-part `−(u−μ)²·8πa·S`, `S := uV`, the combination is
`8πaV·[½u² − μu − u(u−μ)²] − 4πa·u`, whose `−8πaV·u³`-term makes it
CONCAVE for `u ≫ μ` — the form that forced option (b). -/
lemma q0_concave_diagnostic_old_cs (a μ V u : ℝ) (hV : V ≠ 0) :
    (1 / 2 : ℝ) * V⁻¹ * (8 * π * a) * ((u * V) ^ 2 - u * V)
      - (8 * π * a) * μ * (u * V)
      - (u - μ) ^ 2 * (8 * π * a * (u * V))
    = 8 * π * a * V * ((1 / 2 : ℝ) * u ^ 2 - μ * u - u * (u - μ) ^ 2)
      - 4 * π * a * u := by
  field_simp [hV]
  ring

/-- **Typeset (b)-target (record)**: the per-state bound consumed by the
next (windowed/gap) step — `E_s := kinWord + qLHSword` bounded below by the
CONVEX FS-form (repulsion main + FS-shape P-part) minus the LINEAR
`(4·cS1/ℓ³)·qOneMass`-mass, `Corr`-term and `pot_sharp_w1line` masses, with
`kinWord` on the LEFT free to absorb the third line under the a-priori window
(`cnPlus ≤ B`, `N̂/ℓ³ ≤ U`, gap regime) — the exact absorption arithmetic
(`(4S/V)·qOneMass` via the `QMassUpper` q2-side `−μ·qOneMass`-machinery,
`Corr` via `q1_corr_abs_le`, the fsqC1/fsqC2/μ-blocks as in
`gap_absorb_sharp`) is the next recorded step.  The `u`-quadratic here is
CONVEX (`q0_convex_plus_fs_Ppart`); its completion to the A₀-remainder
`¼(u−μ)²·8πaV − ½μ²·8πaV`-form uses `A0Core.a0_form_square_identity`
family. -/
def step4_sqrt_target_statement {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) : Prop :=
  (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2
      - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
      - (1 / 4) * ((((N : ℝ) / ℓ ^ 3) - μ) ^ 2) * ((8 * π * (a v)) * ℓ ^ 3)
      - ((4 * (cS1 ℓ Φ)) / ℓ ^ 3) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
      - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
            (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
    ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ

/-- Crude one-body Q-mass bound: `qOneMass ≤ fsqC1·cnPlus` — pointwise
`0 ≤ f₁ ≤ fsqC1` (fibre sup `|f₁| ≤ fsqC1 = chiSup²·2·8π·a v`, nonneg), so
`qOneMass = Σ∫(Q_iΦ)²f₁(x_i) ≤ fsqC1·Σ∫(Q_iΦ)²`.  The Q-part
`(4S/V)·qOneMass` of the FS-shape CS is therefore LINEAR in `cnPlus` with
coefficient `4·fsqC1·S/V ≤ 4·fsqC1·U` — gap-absorbable in shape under the
density cap (the regime constant is spelled in `step4_third_line_absorbed`). -/
lemma qOneMass_le_fsqC1_mul_cnPlus {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) ≤ (fsqC1 (a v)) * cnPlus ℓ Φ := by
  classical
  let f1 : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g0 v h)) z
  have hf1b : ∀ z : ℝ³, |f1 z| ≤ fsqC1 (a v) := by
    intro z
    dsimp [f1, fsqC1]
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  have hf1nn : ∀ z : ℝ³, 0 ≤ f1 z := by
    intro z
    dsimp [f1]
    exact w1Fibre_nonneg hR hv_nonneg hvrad hv_supp h z
  have hf1le : ∀ z : ℝ³, f1 z ≤ fsqC1 (a v) := by
    intro z
    exact (abs_le.mp (hf1b z)).2
  have hper : ∀ i : Fin N,
      (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i))
        ≤ (fsqC1 (a v)) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
    intro i
    have hQc : Continuous (fun x : X N => aQ ℓ i Φ x) := aQ_continuous hℓ i hΦc
    have hf1m : AEStronglyMeasurable f1 (volume.restrict (acube ℓ)) := by
      dsimp [f1]
      have hfac := fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
      simpa [w1Fibre, wPairC] using hfac
    have hL : Integrable (fun x => (aQ ℓ i Φ x) ^ 2 * f1 (x i))
        (volume.restrict (abox N ℓ)) := by
      have hb := integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z) (hQc.pow 2)
      simpa [IntegrableOn] using hb
    have hfC : AEStronglyMeasurable (fun z : ℝ³ => fsqC1 (a v)) (volume.restrict (acube ℓ)) := by
      exact (MeasureTheory.stronglyMeasurable_const (α := ℝ³) (β := ℝ)
        (b := fsqC1 (a v))).aestronglyMeasurable
    have hCnn : 0 ≤ fsqC1 (a v) := by
      have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
      dsimp [fsqC1]
      positivity
    have hR : Integrable (fun x => (fsqC1 (a v)) * (aQ ℓ i Φ x) ^ 2)
        (volume.restrict (abox N ℓ)) := by
      have hb := integrableOn_slot_fibre hℓ i hfC (C := fsqC1 (a v)) (fun z hz => by simp [abs_of_nonneg hCnn]) (hQc.pow 2)
      simpa [IntegrableOn, mul_comm, mul_left_comm, mul_assoc] using hb
    have hle : (fun x => (aQ ℓ i Φ x) ^ 2 * f1 (x i))
        ≤ fun x => (fsqC1 (a v)) * (aQ ℓ i Φ x) ^ 2 := by
      intro x
      have hf : f1 (x i) ≤ fsqC1 (a v) := hf1le (x i)
      have hq : 0 ≤ (aQ ℓ i Φ x) ^ 2 := sq_nonneg _
      calc
        (aQ ℓ i Φ x) ^ 2 * f1 (x i) ≤ (aQ ℓ i Φ x) ^ 2 * (fsqC1 (a v)) := mul_le_mul_of_nonneg_left hf hq
        _ = (fsqC1 (a v)) * (aQ ℓ i Φ x) ^ 2 := by ring
    have hm := MeasureTheory.integral_mono hL hR hle
    have hRHS : (∫ x in abox N ℓ, (fsqC1 (a v)) * (aQ ℓ i Φ x) ^ 2)
        = (fsqC1 (a v)) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
      simpa using (MeasureTheory.integral_const_mul (μ := volume.restrict (abox N ℓ))
        (r := fsqC1 (a v)) (f := fun x : X N => (aQ ℓ i Φ x) ^ 2))
    calc
      (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i))
          ≤ (∫ x in abox N ℓ, (fsqC1 (a v)) * (aQ ℓ i Φ x) ^ 2) := hm
      _ = (fsqC1 (a v)) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := hRHS
  have hsum : (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i))
      ≤ (∑ i : Fin N, (fsqC1 (a v)) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) :=
    Finset.sum_le_sum (s := Finset.univ) (fun i hi => hper i)
  have hRHS : (∑ i : Fin N, (fsqC1 (a v)) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2))
      = (fsqC1 (a v)) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
    rw [← Finset.mul_sum]
  calc
    qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
        = (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
            simp [qOneMass, f1]
    _ ≤ (∑ i : Fin N, (fsqC1 (a v)) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := hsum
    _ = (fsqC1 (a v)) * cnPlus ℓ Φ := by
            rw [hRHS]
            simp [cnPlus]

/-- **Standalone third-line absorption (assembly certificate)** — closes
`pot_sharp_w1line_cs_fs_repulsion` into an `E_s`-bound with the mass/Q-part
third line absorbed by `kinWord` under the a-priori window and gap regime.

Assumptions (each is either machine-checked or an explicit window to be
verified): (a) the `qOneMass`-part is LINEAR in `cnPlus` with coefficient
`4·fsqC1·(S/V) ≤ 4·fsqC1·U` (from `qOneMass_le_fsqC1_mul_cnPlus` +
`cS1 = N̂−np ≤ N̂` + the density cap `hucap`); (b) the `Corr`-term is
windowed by `2·V⁻¹·|Corr| ≤ kc·cnPlus` (hCorr — the open sub-item: the
Session-154/155 arithmetic shows the crude `√(S·cnPlus)`-bound is NOT
kinWord-gap-absorbable, so (b) requires the fine `Corr`-structure; recorded
as the next research item); (c) the mass tail is cnPlus-linear up to the
explicit cS2-block (leftover, exactly as `gap_absorb_sharp` leaves its
`(C₂+7C₁)·cS2/V`-block); (d) the gap regime `hreg` budgets all the
cnPlus-linear coefficients against the kinetic gap `1/(36ℓ²)`.

Conclusion: `E_s = kinWord + qLHSword ≥` the CONVEX FS-form main minus the
cS2-leftover (and minus the `−¼(u−μ)²·8πaV` P-part, which the next
A0-core assembly completes to the FS remainder form). -/
lemma pot_sharp_w1line_cs_fs_absorbed {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    (hμ : 0 < μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hSc1 : 0 < cS1 ℓ Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    {B U kc : ℝ}
    -- (w1) the a-priori excited-mass window
    (hwinP : cnPlus ℓ Φ ≤ B)
    -- (w2) the density cap
    (hucap : (N : ℝ) / ℓ ^ 3 ≤ U)
    -- Corr-window (the open sub-item; see doc)
    (hCorr : 2 * (ℓ ^ 3)⁻¹ * |∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
          (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)| ≤ kc * cnPlus ℓ Φ)
    -- (d) the gap regime: budgets μC₁, 4C₁U (Q-part), the mass-tail
    -- coefficients (2C₂+3C₁+(8/3)C₁+4C₁)U and kc against 1/(36ℓ²)
    (hreg : μ * (fsqC1 (a v)) + (4 * (fsqC1 (a v)) + (2 * (fsqC2 (a v)) + (3 + 8 / 3 + 4) * (fsqC1 (a v)))) * U + kc
        ≤ 1 / (36 * ℓ ^ 2)) :
    (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
        - (1 / 4) * ((((N : ℝ) / ℓ ^ 3) - μ) ^ 2) * ((8 * π * (a v)) * ℓ ^ 3)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ)
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  classical
  have hΦcc : Continuous Φ := hΦc.continuous
  let S : ℝ := cS1 ℓ Φ
  let V : ℝ := ℓ ^ 3
  let np : ℝ := cnPlus ℓ Φ
  let C₁ : ℝ := fsqC1 (a v)
  let C₂ : ℝ := fsqC2 (a v)
  let Corr : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
        (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)
  let Q : ℝ := qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
  have hE := pot_sharp_w1line_cs_fs_repulsion hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦcc hSc1 hnorm
  have hgap : (1 / (36 * ℓ ^ 2)) * np ≤ kinWord N ℓ Φ := by
    simpa [np] using kinWord_gap_cnPlus hℓ hΦc
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hSnn : 0 ≤ S := by dsimp [S]; exact cS1_nonneg
  have hnpnn : 0 ≤ np := by dsimp [np]; exact cnPlus_nonneg
  have hC1nn : 0 ≤ C₁ := by
    dsimp [C₁, fsqC1]
    positivity
  have hC2nn : 0 ≤ C₂ := by
    dsimp [C₂, fsqC2]
    positivity
  -- qOneMass ≤ C₁·np (crude, machine-checked), S ≤ N̂ (cS1 = N̂ − np), u ≤ U
  have hq1 : Q ≤ C₁ * np := by
    have hb := qOneMass_le_fsqC1_mul_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦcc
    simpa [Q, np, C₁] using hb
  have hSleqN : S ≤ (N : ℝ) := by
    have hSrel := cS1_eq_nat_sub_cnPlus hℓ hΦcc hnorm
    dsimp [S]
    rw [hSrel]
    have hnn : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
    nlinarith
  have hSV : (S / V) ≤ U := by
    dsimp [S, V]
    have hVpos : 0 < ℓ ^ 3 := by positivity
    have hN : (N : ℝ) / ℓ ^ 3 ≤ U := hucap
    have hsu : S / ℓ ^ 3 ≤ (N : ℝ) / ℓ ^ 3 := by
      exact div_le_div_of_nonneg_right hSleqN (le_of_lt hVpos)
    nlinarith
  -- the absorbed cnPlus-linear blocks (np-coefficient budget)
  have hAbs : (4 * (S / V)) * Q + 2 * (ℓ ^ 3)⁻¹ * Corr
        + (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (2 * ((N : ℝ) * np))
        + (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((3 + 8 / 3 + 4) * ((N : ℝ) * np))
        + μ * (fsqC1 (a v)) * np
      ≤ kinWord N ℓ Φ := by
    have hQabs : (4 * (S / V)) * Q ≤ 4 * C₁ * U * np := by
      have h4 : 0 ≤ (4 : ℝ) * (S / V) := mul_nonneg (by norm_num) (div_nonneg hSnn (le_of_lt hVpos))
      have hmul := mul_le_mul_of_nonneg_left hq1 h4
      have hsvc : (4 * (S / V)) * (C₁ * np) ≤ (4 * U) * (C₁ * np) := by
        have h1 : (4 * (S / V)) ≤ 4 * U := by nlinarith [hSV]
        exact mul_le_mul_of_nonneg_right h1 (mul_nonneg hC1nn hnpnn)
      nlinarith [hmul, hsvc]
    have htail1 : (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (2 * ((N : ℝ) * np)) ≤ 2 * C₂ * U * np := by
      have hred : (ℓ ^ 3)⁻¹ * ((N : ℝ) * np) ≤ U * np := by
        have hcn : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
        have hq2 := mul_le_mul_of_nonneg_right hucap hcn
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, np] using hq2
      have hc : 0 ≤ 2 * (fsqC2 (a v)) := by positivity
      have hstep : (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (2 * ((N : ℝ) * np))
          = 2 * (fsqC2 (a v)) * ((ℓ ^ 3)⁻¹ * ((N : ℝ) * np)) := by ring
      rw [hstep]
      have hm2 := mul_le_mul_of_nonneg_left hred hc
      dsimp [C₂]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hm2
    have htail2 : (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((3 + 8 / 3 + 4) * ((N : ℝ) * np))
        ≤ (3 + 8 / 3 + 4) * C₁ * U * np := by
      have hred : (ℓ ^ 3)⁻¹ * ((N : ℝ) * np) ≤ U * np := by
        have hcn : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
        have hq2 := mul_le_mul_of_nonneg_right hucap hcn
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, np] using hq2
      have hc : 0 ≤ (3 + 8 / 3 + 4) * (fsqC1 (a v)) := by positivity
      have hstep : (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((3 + 8 / 3 + 4) * ((N : ℝ) * np))
          = (3 + 8 / 3 + 4) * (fsqC1 (a v)) * ((ℓ ^ 3)⁻¹ * ((N : ℝ) * np)) := by ring
      rw [hstep]
      have hm2 := mul_le_mul_of_nonneg_left hred hc
      dsimp [C₁]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hm2
    have hCorr' : 2 * (ℓ ^ 3)⁻¹ * Corr ≤ kc * np := by
      have hC : 2 * (ℓ ^ 3)⁻¹ * Corr ≤ 2 * (ℓ ^ 3)⁻¹ * |Corr| := by
        have hpos : 0 ≤ 2 * (ℓ ^ 3)⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left (le_abs_self Corr) hpos
      have hb := hCorr
      simpa [Corr, np] using (le_trans hC hb)
    -- sum the cnPlus-linear blocks: coefficient budget ≤ 1/(36ℓ²)
    have hlin : 4 * C₁ * U * np + 2 * C₂ * U * np
          + (3 + 8 / 3 + 4) * C₁ * U * np + μ * C₁ * np + kc * np
        ≤ (1 / (36 * ℓ ^ 2)) * np := by
      have hcn : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
      have hregmul := mul_le_mul_of_nonneg_right hreg hcn
      nlinarith [hregmul]
    have hg' : (1 / (36 * ℓ ^ 2)) * np ≤ kinWord N ℓ Φ := hgap
    nlinarith
  -- assemble: E_s ≥ G := (main) − 4C₁cS2/V, from hE (qLHS ≥ G − Tsum) + hT' (Tsum ≤ kinWord)
  let G : ℝ := (4 * π * (a v) / ℓ ^ 3) * (cS1 ℓ Φ - μ * ℓ ^ 3 - (1 / 2 : ℝ)) ^ 2
      - (4 * π * (a v)) * μ ^ 2 * ℓ ^ 3 * (1 + 1 / (2 * μ * ℓ ^ 3)) ^ 2
      - (1 / 4) * ((((N : ℝ) / ℓ ^ 3) - μ) ^ 2) * ((8 * π * (a v)) * ℓ ^ 3)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ)
  let Tsum : ℝ := ((4 * (cS1 ℓ Φ)) / ℓ ^ 3) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
      + 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
            (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))
      + (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (2 * ((N : ℝ) * cnPlus ℓ Φ))
      + (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((3 + 8 / 3 + 4) * ((N : ℝ) * cnPlus ℓ Φ))
      + μ * (fsqC1 (a v)) * cnPlus ℓ Φ
  have hT' : Tsum ≤ kinWord N ℓ Φ := by
    have hb := hAbs
    dsimp [S, V, np, C₁, C₂, Q, Corr] at hb
    have hqq : (4 * (cS1 ℓ Φ / ℓ ^ 3)) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
        = ((4 * (cS1 ℓ Φ)) / ℓ ^ 3) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
      ring
    rw [hqq] at hb
    simpa [Tsum] using hb
  have hE2 : G - Tsum + kinWord N ℓ Φ ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    dsimp [G, Tsum]
    nlinarith [hE]
  have hGle : G ≤ G - Tsum + kinWord N ℓ Φ := by
    nlinarith [hT']
  simpa [G] using (le_trans hGle hE2)

end BoseGases

end Submission
