import ChallengeDeps
import Submission.Work.FSKernelCompare
import Submission.Work.Q2Mass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# L2 — the corpus eq:Q1n0 collapse: q1-word pair-part peel atoms

FS `lm:appinteractionestimate`/`lem:QDecompSimpler` (eq:Q1n0): q1word's pair
part `2Σ_{i≠j}∫(P_iQ_jΦ)(P_iP_jΦ)·w₂(x_i,x_j)` collapses (P-constancy +
`Σ_jP_j = n₀`-sandwich) to the one-body `(n₀/V)-weighted` Q–P crosses with
the `w₂`-fibre — the exact content that (a) feeds the A₀ quadratic
`−¼(μ−u−1/V)²·8πaV` after the Step-4 CS and (b) cancels the Q3+Q4CS
PPQω-leftover.  Design note Session-126 addendum carries the full derivation
(L2a per-pair, L2b per-slot sum, L2c total); this module implements its
atoms, starting with the fibre-regularity enabler:

* `aP_const_mul_weight` / `aP_aQ_zero` — pointwise projection algebra with a
  weight (slot-i-only weight pulls through `P_j`, `i ≠ j`);
  `P_j(Q_jΦ) = 0` pointwise;
* `aP_sym_weight` — the P-adjointness against a slot-i-only (bounded, aem)
  weight over slot `j` (i ≠ j): `∫(P_jX)(w(x_i)·Y) = ∫X·(w(x_i)·P_jY)`
  — the generalisation of `Q0Sector.aP_sym_box` needed because the `w₂`-fibre
  `fibre₂(x_i) := w1Fibre(g2)(x_i)` is not continuous, only aem + bounded
  (`integrableOn_slot_fibre`, `fibre_acube_aem`);
* `q1_ortho` — the per-pair annihilation
  `∫(P_jQ_iΦ)(P_iQ_jΦ)·w(x_i) = 0` (`i ≠ j`, slot-i weight): via
  `aP_sym_weight` + `P_jP_iQ_jΦ = 0`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `P_j(Q_jΦ) = 0` pointwise (projections are complementary). -/
lemma aP_aQ_zero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) (x : X N) :
    aP ℓ j (aQ ℓ j Φ) x = 0 := by
  have hPjc : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
  have hsub := aP_sub hℓ j (Φ := Φ) (Ψ := aP ℓ j Φ) hΦc hPjc x
  have hA : aQ ℓ j Φ = Φ - aP ℓ j Φ := by funext y; rfl
  calc
    aP ℓ j (aQ ℓ j Φ) x = aP ℓ j Φ x - aP ℓ j (aP ℓ j Φ) x := by
      rw [hA]
      exact hsub
    _ = aP ℓ j Φ x - aP ℓ j Φ x := by rw [aP_idem hℓ j hΦc x]
    _ = 0 := by ring

/-- A slot-i-only weight pulls through `P_j` (`i ≠ j`): pointwise
`P_j[ w(x_i)·Y ] = w(x_i)·P_j Y` (pure algebra — `P_j` only averages the
`j`-coordinate, which `w(x_i)` does not touch). -/
lemma aP_const_mul_weight {N : ℕ} {ℓ : ℝ} {i j : Fin N} (hij : i ≠ j)
    (w : ℝ³ → ℝ) {F : X N → ℝ} (x : X N) :
    aP ℓ j (fun z : X N => w (z i) * F z) x = w (x i) * aP ℓ j F x := by
  have hw : ∀ y : ℝ³, w ((Function.update x j y) i) = w (x i) := by
    intro y
    have hne : i ≠ j := hij
    -- update at slot j leaves slot i unchanged
    simp [Function.update, hne]
  have hWf : (fun y : ℝ³ => w ((Function.update x j y) i) * F (Function.update x j y))
      = fun y : ℝ³ => w (x i) * F (Function.update x j y) := by
    funext y
    rw [hw y]
  calc
    aP ℓ j (fun z : X N => w (z i) * F z) x
        = (1 / ℓ ^ 3) * (∫ y in acube ℓ,
            w ((Function.update x j y) i) * F (Function.update x j y)) := by
            unfold aP
            rfl
    _ = (1 / ℓ ^ 3) * (∫ y in acube ℓ, w (x i) * F (Function.update x j y)) := by
            rw [hWf]
    _ = w (x i) * ((1 / ℓ ^ 3) * (∫ y in acube ℓ, F (Function.update x j y))) := by
            rw [integral_const_mul]
            ring
    _ = w (x i) * aP ℓ j F x := by
            unfold aP
            rfl

/-- **Weighted `P`-adjointness** (`i ≠ j`): for a slot-`i`-only weight `w`
(only aem + bounded on the cube — the `w₂`-fibre is NOT continuous),

`∫ (aP_j X)·(w(x_i)·Y) = ∫ X·(w(x_i)·(aP_j Y))`.

Generalisation of `Q0Sector.aP_sym_box` (which needs both factors
continuous); this is the fibre-regularity enabler for the q1-pair
orthogonality and the q3-cross work. -/
lemma aP_sym_weight {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    (w : ℝ³ → ℝ) {C : ℝ} (hFm : AEStronglyMeasurable w (volume.restrict (acube ℓ)))
    (hC : ∀ z : ℝ³, z ∈ acube ℓ → |w z| ≤ C)
    {Φ Ψ : X N → ℝ} (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in abox N ℓ, (aP ℓ j Φ x) * (w (x i) * Ψ x))
      = ∫ x in abox N ℓ, Φ x * (w (x i) * (aP ℓ j Ψ x)) := by
  -- both integrands are slot-i-fibres of a continuous factor
  have hS1 : Continuous (fun x : X N => (aP ℓ j Φ x) * Ψ x) :=
    (aP_continuous hℓ j hΦc).mul hΨc
  have hS2 : Continuous (fun x : X N => Φ x * (aP ℓ j Ψ x)) :=
    hΦc.mul (aP_continuous hℓ j hΨc)
  have hInt1 : IntegrableOn (fun x : X N => (aP ℓ j Φ x) * (w (x i) * Ψ x))
      (abox N ℓ) volume := by
    have h1 := integrableOn_slot_fibre hℓ i hFm hC hS1
    simpa [mul_assoc, mul_left_comm, mul_comm] using h1
  have hInt2 : IntegrableOn (fun x : X N => Φ x * (w (x i) * (aP ℓ j Ψ x)))
      (abox N ℓ) volume := by
    have h1 := integrableOn_slot_fibre hℓ i hFm hC hS2
    simpa [mul_assoc, mul_left_comm, mul_comm] using h1
  -- peel slot `j` on both sides; the weight w(x_i) is constant in slot j
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero j.1 j.isLt
  | succ n =>
      have hP1 := abox_integral_peel (n := n) (i := j)
        (F := fun x : X (n + 1) => (aP ℓ j Φ x) * (w (x i) * Ψ x)) hInt1
      have hP2 := abox_integral_peel (n := n) (i := j)
        (F := fun x : X (n + 1) => Φ x * (w (x i) * (aP ℓ j Ψ x))) hInt2
      have hci : ∀ (r : X n) (y : ℝ³),
          (kcInsN n j (y, r)) i = (kcInsN n j (0, r)) i := by
        intro r y
        exact kc_insN_other_indep n j y 0 r i hij
      have hpoint : ∀ r : X n,
          (∫ y in acube ℓ, (aP ℓ j Φ (kcInsN n j (y, r))) * (w ((kcInsN n j (y, r)) i) * Ψ (kcInsN n j (y, r))))
            = (∫ y in acube ℓ, Φ (kcInsN n j (y, r)) * (w ((kcInsN n j (y, r)) i) * (aP ℓ j Ψ (kcInsN n j (y, r))))) := by
        intro r
        let ci : ℝ³ := (kcInsN n j (0, r)) i
        let CX : ℝ := (1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n j (z, r)))
        let CY : ℝ := (1 / ℓ ^ 3) * (∫ z in acube ℓ, Ψ (kcInsN n j (z, r)))
        have hXcst : ∀ y : ℝ³, aP ℓ j Φ (kcInsN n j (y, r)) = CX := by
          intro y
          dsimp [CX]
          exact aP_kcInsN (i := j) y r
        have hYcst : ∀ y : ℝ³, aP ℓ j Ψ (kcInsN n j (y, r)) = CY := by
          intro y
          dsimp [CY]
          exact aP_kcInsN (i := j) y r
        let wci : ℝ := w ((kcInsN n j (0, r)) i)
        have hwci : ∀ y : ℝ³, w ((kcInsN n j (y, r)) i) = wci := by
          intro y
          dsimp [wci]
          exact congrArg w (hci r y)
        have hL : (∫ y in acube ℓ,
              (aP ℓ j Φ (kcInsN n j (y, r))) * (w ((kcInsN n j (y, r)) i) * Ψ (kcInsN n j (y, r))))
            = (wci * CX) * (∫ y in acube ℓ, Ψ (kcInsN n j (y, r))) := by
          calc
            (∫ y in acube ℓ,
                (aP ℓ j Φ (kcInsN n j (y, r))) * (w ((kcInsN n j (y, r)) i) * Ψ (kcInsN n j (y, r))))
                = ∫ y in acube ℓ, wci * (CX * Ψ (kcInsN n j (y, r))) := by
                    apply integral_congr_ae
                    refine ae_of_all _ (fun y => ?_)
                    change aP ℓ j Φ (kcInsN n j (y, r)) *
                        (w ((kcInsN n j (y, r)) i) * Ψ (kcInsN n j (y, r)))
                        = wci * (CX * Ψ (kcInsN n j (y, r)))
                    rw [hXcst y, hwci y]
                    ring
            _ = (wci * CX) * (∫ y in acube ℓ, Ψ (kcInsN n j (y, r))) := by
                    calc
                      (∫ y in acube ℓ, wci * (CX * Ψ (kcInsN n j (y, r))))
                          = ∫ y in acube ℓ, (wci * CX) * Ψ (kcInsN n j (y, r)) := by
                              apply integral_congr_ae
                              refine ae_of_all _ (fun y => ?_)
                              ring
                      _ = (wci * CX) * (∫ y in acube ℓ, Ψ (kcInsN n j (y, r))) := by
                              rw [integral_const_mul]
        have hR : (∫ y in acube ℓ,
              Φ (kcInsN n j (y, r)) * (w ((kcInsN n j (y, r)) i) * (aP ℓ j Ψ (kcInsN n j (y, r)))))
            = (wci * CY) * (∫ y in acube ℓ, Φ (kcInsN n j (y, r))) := by
          calc
            (∫ y in acube ℓ,
                Φ (kcInsN n j (y, r)) * (w ((kcInsN n j (y, r)) i) * (aP ℓ j Ψ (kcInsN n j (y, r)))))
                = ∫ y in acube ℓ, wci * (Φ (kcInsN n j (y, r)) * CY) := by
                    apply integral_congr_ae
                    refine ae_of_all _ (fun y => ?_)
                    change Φ (kcInsN n j (y, r)) *
                        (w ((kcInsN n j (y, r)) i) * (aP ℓ j Ψ (kcInsN n j (y, r))))
                        = wci * (Φ (kcInsN n j (y, r)) * CY)
                    rw [hwci y, hYcst y]
                    ring
            _ = (wci * CY) * (∫ y in acube ℓ, Φ (kcInsN n j (y, r))) := by
                    calc
                      (∫ y in acube ℓ, wci * (Φ (kcInsN n j (y, r)) * CY))
                          = ∫ y in acube ℓ, (wci * CY) * Φ (kcInsN n j (y, r)) := by
                              apply integral_congr_ae
                              refine ae_of_all _ (fun y => ?_)
                              ring
                      _ = (wci * CY) * (∫ y in acube ℓ, Φ (kcInsN n j (y, r))) := by
                              rw [integral_const_mul]
        have hCX : CX * (∫ y in acube ℓ, Ψ (kcInsN n j (y, r)))
            = CY * (∫ y in acube ℓ, Φ (kcInsN n j (y, r))) := by
          have hCX' : CX = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n j (y, r))) := by
            dsimp [CX]
          have hCY' : CY = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Ψ (kcInsN n j (y, r))) := by
            dsimp [CY]
          rw [hCX', hCY']
          ring
        calc
          (∫ y in acube ℓ,
              (aP ℓ j Φ (kcInsN n j (y, r))) * (w ((kcInsN n j (y, r)) i) * Ψ (kcInsN n j (y, r))))
              = (wci * CX) * (∫ y in acube ℓ, Ψ (kcInsN n j (y, r))) := hL
          _ = (wci * CY) * (∫ y in acube ℓ, Φ (kcInsN n j (y, r))) := by
                  rw [mul_assoc, hCX, ← mul_assoc]
          _ = (∫ y in acube ℓ,
              Φ (kcInsN n j (y, r)) * (w ((kcInsN n j (y, r)) i) * (aP ℓ j Ψ (kcInsN n j (y, r))))) := hR.symm
      calc
        (∫ x in abox (n + 1) ℓ, (aP ℓ j Φ x) * (w (x i) * Ψ x))
            = ∫ r : X n, (∫ y in acube ℓ,
                (aP ℓ j Φ (kcInsN n j (y, r))) * (w ((kcInsN n j (y, r)) i) * Ψ (kcInsN n j (y, r))))
                ∂((volume : Measure (X n)).restrict (abox n ℓ)) := hP1
        _ = ∫ r : X n, (∫ y in acube ℓ,
                Φ (kcInsN n j (y, r)) * (w ((kcInsN n j (y, r)) i) * (aP ℓ j Ψ (kcInsN n j (y, r)))))
                ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
                apply integral_congr_ae
                refine ae_of_all _ (fun r => ?_)
                exact hpoint r
        _ = (∫ x in abox (n + 1) ℓ, Φ x * (w (x i) * (aP ℓ j Ψ x))) := hP2.symm

/-- `P_j(P_i(Q_jΦ)) = 0` pointwise (`i ≠ j`): the annihilation behind the
q1-pair orthogonality. -/
lemma aP_aP_aQ_zero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (_hij : i ≠ j)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (x : X N) :
    aP ℓ j (aP ℓ i (aQ ℓ j Φ)) x = 0 := by
  have hQc : Continuous (aQ ℓ j Φ) := aQ_continuous hℓ j hΦc
  have hPic : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i hQc
  calc
    aP ℓ j (aP ℓ i (aQ ℓ j Φ)) x = aP ℓ i (aP ℓ j (aQ ℓ j Φ)) x := aP_comm hℓ j i hQc x
    _ = aP ℓ i (fun z : X N => 0) x := by
          congr 1
          funext z
          exact aP_aQ_zero hℓ j hΦc z
    _ = 0 := by
          simp [aP]

/-- **Per-pair q1 orthogonality** (`i ≠ j`, slot-`i`-only weight `w`):
`∫ (P_jQ_iΦ)·(P_iQ_jΦ)·w(x_i) = 0` — the identity that lets the q1-pair
peel replace `P_jP_iΦ` by `P_iΦ` (L2a, design note Session-126).  Via the
weighted adjointness `aP_sym_weight` + `P_jP_iQ_jΦ = 0`. -/
lemma q1_ortho {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    (w : ℝ³ → ℝ) {C : ℝ} (hFm : AEStronglyMeasurable w (volume.restrict (acube ℓ)))
    (hC : ∀ z : ℝ³, z ∈ acube ℓ → |w z| ≤ C)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * w (x i)) = 0 := by
  classical
  have hQic : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hQjc : Continuous (aQ ℓ j Φ) := aQ_continuous hℓ j hΦc
  have hPQc : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i hQjc
  have hadj := aP_sym_weight (N := N) (ℓ := ℓ) hℓ (i := i) (j := j) hij w hFm hC
    (Φ := aQ ℓ i Φ) (Ψ := aP ℓ i (aQ ℓ j Φ)) hQic hPQc
  have hmain : (∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) * (w (x i) * (aP ℓ i (aQ ℓ j Φ) x)))
      = 0 := by
    rw [hadj]
    have hzero : ∀ x : X N, (aQ ℓ i Φ x) * (w (x i) * (aP ℓ j (aP ℓ i (aQ ℓ j Φ)) x)) = 0 := by
      intro x
      rw [aP_aP_aQ_zero hℓ hij hΦc x]
      ring
    calc
      (∫ x in abox N ℓ, (aQ ℓ i Φ x) * (w (x i) * (aP ℓ j (aP ℓ i (aQ ℓ j Φ)) x)))
          = ∫ x in abox N ℓ, 0 := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              exact hzero x
      _ = 0 := by simp
  calc
    (∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * w (x i))
        = ∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) * (w (x i) * (aP ℓ i (aQ ℓ j Φ) x)) := by
            apply integral_congr_ae
            refine ae_of_all _ (fun x => ?_)
            ring
    _ = 0 := hmain

/-- Integrability over `abox (p+2) ℓ` of the q1-pair LHS integrand
`(P_jQ_iΦ)·(P_jP_iΦ)·w₂(x_j,x_i)` (`w₂ := wPairC(g2)`, `i ≠ j`; the
`Q2Mass.q2QQ_F_integrable` clone with the square replaced by the two-factor
product). -/
lemma q1F_int {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (g2 v h) (x j) (x i))
      (abox (p + 2) ℓ) volume := by
  classical
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hPψc : Continuous (fun x : X (p + 2) => aP ℓ j (aQ ℓ i Φ) x) :=
    aP_continuous hℓ j hψc
  have hPc : Continuous (fun x : X (p + 2) => aP ℓ j (aP ℓ i Φ) x) :=
    aP_continuous hℓ j (aP_continuous hℓ i hΦc)
  have hSc : Continuous (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) := hPψc.mul hPc
  obtain ⟨B, hB⟩ := (abox_compact (p + 2) hℓ).exists_bound_of_continuousOn
    (s := abox (p + 2) ℓ)
    (f := fun x : X (p + 2) => (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x))
    hSc.continuousOn
  have hw2i : IntegrableOn (wPairU ℓ (g2 v h)) (acube ℓ ×ˢ acube ℓ) volume :=
    integrableOn_w2c_acube hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  have hwcomp : IntegrableOn (fun x : X (p + 2) => wPairU ℓ (g2 v h) (x j, x i))
      (abox (p + 2) ℓ) volume :=
    integrableOn_pair_comp_ae hℓ j i hij.symm hw2i
  have hwabs : Integrable (fun x : X (p + 2) => |wPairU ℓ (g2 v h) (x j, x i)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    have hwabs' := hwcomp.abs
    simpa [Real.norm_eq_abs] using hwabs'
  have hbnd : ∀ᵐ x ∂(volume.restrict (abox (p + 2) ℓ)),
      ‖((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) *
          wPairU ℓ (g2 v h) (x j, x i)‖
        ≤ B * |wPairU ℓ (g2 v h) (x j, x i)| := by
    rw [ae_restrict_iff' (abox_measurable (p + 2) ℓ)]
    apply ae_of_all
    intro x hx
    have hle : |(aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)| ≤ B := by
      have hb' := hB x hx
      simpa [Real.norm_eq_abs] using hb'
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hmeas : AEStronglyMeasurable (fun x : X (p + 2) =>
      ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) *
          wPairU ℓ (g2 v h) (x j, x i))
      (volume.restrict (abox (p + 2) ℓ)) := by
    exact hSc.aestronglyMeasurable.mul hwcomp.aestronglyMeasurable
  have hdomin : Integrable (fun x : X (p + 2) => B * |wPairU ℓ (g2 v h) (x j, x i)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    exact hwabs.const_mul B
  have hgoal : Integrable (fun x : X (p + 2) =>
      ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) * wPairC ℓ (g2 v h) (x j) (x i))
      (volume.restrict (abox (p + 2) ℓ)) := by
    change Integrable (fun x : X (p + 2) =>
        ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) * wPairU ℓ (g2 v h) (x j, x i))
      (volume.restrict (abox (p + 2) ℓ))
    exact Integrable.mono' hdomin hmeas hbnd
  exact hgoal

/-- Integrability over `abox (p+2) ℓ` of the q1-pair RHS integrand
`(P_jQ_iΦ)·(P_iΦ)·fibre₂(x_i)` (`fibre₂ := w1Fibre(wPairC(g2))`, `i ≠ j`). -/
lemma q1G_int {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (_hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))
      (abox (p + 2) ℓ) volume := by
  classical
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hS : Continuous (fun x : X (p + 2) => (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)) :=
    (aP_continuous hℓ j hψc).mul (aP_continuous hℓ i hΦc)
  have hFm : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ (g2 v h)) z)
      (volume.restrict (acube ℓ)) := by
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := g2 v h)
      (g2_integrable hR hv_nonneg hvrad hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
      |w1Fibre ℓ (wPairC ℓ (g2 v h)) z| ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
    intro z hz
    have hb := w2c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  exact integrableOn_slot_fibre hℓ i hFm hbnd hS


/-- **q1-pair peel (L2a core)**: with `A := P_jQ_iΦ`, `B := P_jP_iΦ`
(`i` = Q/fibre slot, `j` = P/peel slot, `w₂ := wPairC(g2)`),
`∫ A·B·w₂(x_j,x_i) = (ℓ³)⁻¹·∫ A·B·fibre₂(x_i)` (`fibre₂ := w1Fibre(g2)`)
— the `Q2Mass.q2QQ_lhs_closed` calc with the square `(P_jψ)²` replaced by
the product `A·B` (both factors constant in slot `j`; peel over `j`, fibre
at `x_i` by `w2_fibre_first_slot_eq`). -/
lemma q1_lhs_closed {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (g2 v h) (x j) (x i))
    = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
  classical
  let F : X (p + 2) → ℝ := fun x =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (g2 v h) (x j) (x i)
  let G : X (p + 2) → ℝ := fun x =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))
  have hF : IntegrableOn F (abox (p + 2) ℓ) volume := by
    simpa [F] using (q1F_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc)
  have hG : IntegrableOn G (abox (p + 2) ℓ) volume := by
    classical
    have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
    have hS : Continuous (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j hψc).mul (aP_continuous hℓ j (aP_continuous hℓ i hΦc))
    have hFm : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ (g2 v h)) z)
        (volume.restrict (acube ℓ)) := by
      have hfac := fibre_acube_aem (ℓ := ℓ) (h := g2 v h)
        (g2_integrable hR hv_nonneg hvrad hv_supp h)
      simpa [w1Fibre, wPairC] using hfac
    have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
        |w1Fibre ℓ (wPairC ℓ (g2 v h)) z| ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
      intro z hz
      have hb := w2c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
      simpa [w1Fibre, wPairC] using hb
    have hInt := integrableOn_slot_fibre hℓ i hFm hbnd hS
    simpa [G] using hInt
  have hpeelF : (∫ x in abox (p + 2) ℓ, F x)
      = ∫ r : X (p + 1), (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) :=
      abox_integral_peel (n := p + 1) (i := j) (F := F) hF
  have hpeelG : (∫ x in abox (p + 2) ℓ, G x)
      = ∫ r : X (p + 1), (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) :=
      abox_integral_peel (n := p + 1) (i := j) (F := G) hG
  have hci : ∀ (r : X (p + 1)) (y : ℝ³),
      (kcInsN (p + 1) j (y, r)) i = (kcInsN (p + 1) j (0, r)) i := by
    intro r y
    exact kc_insN_other_indep (p + 1) j y 0 r i hij
  have hinner : ∀ r : X (p + 1),
      (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
        = (ℓ ^ 3)⁻¹ * (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r))) := by
    intro r
    let ci : ℝ³ := (kcInsN (p + 1) j (0, r)) i
    let CA : ℝ := (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, (aQ ℓ i Φ) (kcInsN (p + 1) j (z, r)))
    let CB : ℝ := (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, (aP ℓ i Φ) (kcInsN (p + 1) j (z, r)))
    have hFibre : (∫ y in acube ℓ, wPair ℓ (g2 v h) y ci) = w1Fibre ℓ (wPairC ℓ (g2 v h)) ci :=
      w2_fibre_first_slot_eq hvrad h ci
    have hAcst : ∀ y : ℝ³, aP ℓ j (aQ ℓ i Φ) (kcInsN (p + 1) j (y, r)) = CA := by
      intro y
      dsimp [CA]
      simpa using (aP_kcInsN (ℓ := ℓ) (i := j) (Φ := aQ ℓ i Φ) y r)
    have hBcst : ∀ y : ℝ³, aP ℓ j (aP ℓ i Φ) (kcInsN (p + 1) j (y, r)) = CB := by
      intro y
      dsimp [CB]
      simpa using (aP_kcInsN (ℓ := ℓ) (i := j) (Φ := aP ℓ i Φ) y r)
    have hFy : (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
        = CA * CB * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci := by
      calc
        (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
            = ∫ y in acube ℓ,
                (aP ℓ j (aQ ℓ i Φ) (kcInsN (p + 1) j (y, r))) *
                  (aP ℓ j (aP ℓ i Φ) (kcInsN (p + 1) j (y, r))) *
                  wPairC ℓ (g2 v h) (kcInsN (p + 1) j (y, r) j) (kcInsN (p + 1) j (y, r) i) := by
                dsimp [F]
        _ = ∫ y in acube ℓ, CA * CB * wPairC ℓ (g2 v h) y ci := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                dsimp [F]
                have hyj : (kcInsN (p + 1) j (y, r)) j = y := kc_insN_apply_same (p + 1) j y r
                rw [hAcst y, hBcst y, hyj, hci r y]
        _ = CA * CB * (∫ y in acube ℓ, wPairC ℓ (g2 v h) y ci) := by
                rw [integral_const_mul]
        _ = CA * CB * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci := by
                rw [← hFibre]
                simp [wPairC]
    have hGy : (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
        = (ℓ ^ 3) * CA * CB * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci := by
      calc
        (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
            = ∫ y in acube ℓ,
                (aP ℓ j (aQ ℓ i Φ) (kcInsN (p + 1) j (y, r))) *
                  (aP ℓ j (aP ℓ i Φ) (kcInsN (p + 1) j (y, r))) *
                  (w1Fibre ℓ (wPairC ℓ (g2 v h)) (kcInsN (p + 1) j (y, r) i)) := by
                dsimp [G]
        _ = ∫ y in acube ℓ, CA * CB * (w1Fibre ℓ (wPairC ℓ (g2 v h)) ci) := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                dsimp [G]
                rw [hAcst y, hBcst y, hci r y]
        _ = (ℓ ^ 3) * CA * CB * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci := by
                rw [integral_const_acube ℓ hℓ (CA * CB * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci)]
                ring
    rw [hFy, hGy]
    field_simp [ne_of_gt hℓ]
  calc
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (g2 v h) (x j) (x i))
        = ∫ x in abox (p + 2) ℓ, F x := by
            simp [F]
    _ = ∫ r : X (p + 1), (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := hpeelF
    _ = ∫ r : X (p + 1), (ℓ ^ 3)⁻¹ * (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := by
            apply integral_congr_ae
            refine ae_of_all _ (fun r => ?_)
            exact hinner r
    _ = (ℓ ^ 3)⁻¹ * ∫ r : X (p + 1), (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := by
            rw [integral_const_mul]
    _ = (ℓ ^ 3)⁻¹ * ∫ x in abox (p + 2) ℓ, G x := by
            rw [hpeelG]
    _ = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
            simp [G]


/-- **q1-pair replacement** (`i ≠ j`, slot-`i`-fibre weight): inside the
`w₂`-fibre integral the condensate-pair factor `P_jP_iΦ` of the q1-pair
integrand may be replaced by `P_iΦ`:

`∫ (P_jQ_iΦ)(P_jP_iΦ)·fibre₂(x_i) = ∫ (P_jQ_iΦ)(P_iΦ)·fibre₂(x_i)`

(difference `= −∫(P_jQ_iΦ)(P_iQ_jΦ)·fibre₂(x_i) = 0` by `q1_ortho`). -/
lemma q1_pair_replace {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))
    = (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
  classical
  let w : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g2 v h)) z
  have hFm : AEStronglyMeasurable w (volume.restrict (acube ℓ)) := by
    dsimp [w]
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := g2 v h)
      (g2_integrable hR hv_nonneg hvrad hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hC : ∀ z : ℝ³, z ∈ acube ℓ → |w z| ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
    intro z hz
    dsimp [w]
    have hb := w2c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  have hortho := q1_ortho hℓ hij (w := w) (C := chiSup ^ 2 * 2 * (16 * π * a v)) hFm hC hΦc
  have hBpt : ∀ x : X (p + 2),
      aP ℓ j (aP ℓ i Φ) x - aP ℓ i Φ x = - (aP ℓ i (aQ ℓ j Φ) x) := by
    intro x
    have hPjc : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
    have hcomm := aP_comm hℓ j i hΦc x
    have hsub := aP_sub hℓ i (Φ := Φ) (Ψ := aP ℓ j Φ) hΦc hPjc x
    have hA : aQ ℓ j Φ = Φ - aP ℓ j Φ := by funext y; rfl
    calc
      aP ℓ j (aP ℓ i Φ) x - aP ℓ i Φ x
          = aP ℓ i (aP ℓ j Φ) x - aP ℓ i Φ x := by rw [hcomm]
      _ = - (aP ℓ i Φ x - aP ℓ i (aP ℓ j Φ) x) := by ring
      _ = - (aP ℓ i (aQ ℓ j Φ) x) := by
              rw [hA]
              rw [← aP_sub hℓ i hΦc hPjc x]
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hS1 : Continuous (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) :=
    (aP_continuous hℓ j hψc).mul (aP_continuous hℓ j (aP_continuous hℓ i hΦc))
  have hIntAB : IntegrableOn (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * (w (x i)))
      (abox (p + 2) ℓ) volume := by
    have h1 := integrableOn_slot_fibre hℓ i hFm hC hS1
    simpa [w] using h1
  have hIntAP : IntegrableOn (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w (x i)))
      (abox (p + 2) ℓ) volume := by
    have h1 := q1G_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc
    simpa [w] using h1
  have hdiff : (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * (w (x i)))
      - (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w (x i))) = 0 := by
    have hsub := integral_sub hIntAB hIntAP
    -- hsub : ∫AB·w − ∫AP·w = ∫(AB·w − AP·w)
    have hbody : (fun x : X (p + 2) =>
          ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) - (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)) * (w (x i)))
        = fun x : X (p + 2) =>
          - ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * (w (x i))) := by
      funext x
      have hB := hBpt x
      have hfac : (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)
            - (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)
          = (aP ℓ j (aQ ℓ i Φ) x) * ((aP ℓ j (aP ℓ i Φ) x) - (aP ℓ i Φ x)) := by ring
      rw [hfac, hB]
      ring
    calc
      (∫ x in abox (p + 2) ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * (w (x i)))
          - (∫ x in abox (p + 2) ℓ,
              (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w (x i)))
          = ∫ x in abox (p + 2) ℓ,
              ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * (w (x i)))
              - ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w (x i))) := hsub.symm
      _ = ∫ x in abox (p + 2) ℓ,
              ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) - (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)) * (w (x i)) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              ring
      _ = ∫ x in abox (p + 2) ℓ,
          - ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * (w (x i))) := by
              rw [hbody]
      _ = 0 := by
              have hneg : (∫ x in abox (p + 2) ℓ,
                  - ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * (w (x i))))
                  = - (∫ x in abox (p + 2) ℓ,
                      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * (w (x i))) := by
                    rw [integral_neg]
              rw [hneg]
              rw [hortho]
              ring
  have hgoal : (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))
      = (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
    simpa [w] using (sub_eq_zero.mp hdiff)
  exact hgoal

/-- **L2a — the q1-pair peel (full)**: `∫ (P_jQ_iΦ)(P_jP_iΦ)·w₂(x_j,x_i)
= (ℓ³)⁻¹·∫ (P_jQ_iΦ)(P_iΦ)·fibre₂(x_i)` (`i` = Q/fibre slot, `j` = P/peel
slot) — from `q1_lhs_closed` (peel) + `q1_pair_replace` (P_jP_iΦ ↦ P_iΦ). -/
lemma q1_pair_peel {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (g2 v h) (x j) (x i))
    = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
  classical
  have hpeel := q1_lhs_closed hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc
  have hrep := q1_pair_replace hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc
  rw [hpeel]
  rw [hrep]


/-- **Per-Q-slot q1-pair sum (L2b)**: summing the per-pair peel `q1_pair_peel`
over `j ≠ i` collapses the RHS into the `(Σ_{j≠i}P_j)(Q_iΦ)`-sandwich:

`Σ_{j≠i} ∫ (P_jQ_iΦ)(P_jP_iΦ)·w₂(x_j,x_i)
  = (ℓ³)⁻¹·∫ (P_iΦ)·fibre₂(x_i)·(Σ_{j≠i}(P_jQ_iΦ))`

(`ψ := Q_iΦ`, `w₂ := wPairC(g2)`, `fibre₂ := w1Fibre(g2)`; the `Σ_{j≠i}`
is written with `if`-guarded `Finset` sums).  With the pointwise collapse
`Σ_{j≠i}P_jQ_iΦ = Q_i((n₀−P_i)Φ)` (`aP_aQ_comm`) this is the FS
eq:Q1n0 `n₀`-sandwich per Q-slot. -/
lemma q1_pair_sum_slot {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin (p + 2))
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∑ j : Fin (p + 2), if _hj : j ≠ i then
        (∫ x in abox (p + 2) ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (g2 v h) (x j) (x i))
        else 0)
    = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (∑ j : Fin (p + 2), if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
  classical
  let ψ : X (p + 2) → ℝ := aQ ℓ i Φ
  let s : Finset (Fin (p + 2)) := Finset.univ.filter (fun j => j ≠ i)
  let lhs_j : Fin (p + 2) → ℝ := fun j =>
      ∫ x in abox (p + 2) ℓ,
        (aP ℓ j ψ x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (g2 v h) (x j) (x i)
  let rhs_j : Fin (p + 2) → ℝ := fun j =>
      ∫ x in abox (p + 2) ℓ,
        (aP ℓ j ψ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))
  have hpair : ∀ j : Fin (p + 2), j ∈ s → lhs_j j = (ℓ ^ 3)⁻¹ * rhs_j j := by
    intro j hj
    have hji : j ≠ i := by
      simpa [s] using (Finset.mem_filter.mp hj).2
    have hpp := q1_pair_peel (p := p) hℓ hv_nonneg hvrad hR hv_supp h hRℓ
      (i := i) (j := j) hji.symm hΦc
    dsimp [lhs_j, rhs_j, ψ]
    rw [hpp]
  have hfint : ∀ j : Fin (p + 2), j ∈ s →
      MeasureTheory.Integrable (fun x : X (p + 2) =>
        (aP ℓ j ψ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))
        (volume.restrict (abox (p + 2) ℓ)) := by
    intro j hj
    have hji : j ≠ i := by
      simpa [s] using (Finset.mem_filter.mp hj).2
    have h1 := q1G_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hji.symm hΦc
    dsimp [ψ]
    change Integrable (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))
      (volume.restrict (abox (p + 2) ℓ))
    exact h1
  have hswap : (∑ j ∈ s, rhs_j j)
      = ∫ x in abox (p + 2) ℓ,
          (∑ j ∈ s, aP ℓ j ψ x) * ((aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
    calc
      (∑ j ∈ s, rhs_j j)
          = ∫ x in abox (p + 2) ℓ,
              (∑ j ∈ s, (aP ℓ j ψ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
              rw [← integral_finsetSum s hfint]
      _ = ∫ x in abox (p + 2) ℓ,
              (∑ j ∈ s, (aP ℓ j ψ x) * ((aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              apply Finset.sum_congr rfl
              intro j _hj
              rw [mul_assoc]
      _ = ∫ x in abox (p + 2) ℓ,
          (∑ j ∈ s, aP ℓ j ψ x) * ((aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              change (∑ j ∈ s, (aP ℓ j ψ x) * ((aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))))
                  = (∑ j ∈ s, aP ℓ j ψ x) * ((aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))
              rw [Finset.sum_mul]
  calc
    (∑ j : Fin (p + 2), if hj : j ≠ i then
        (∫ x in abox (p + 2) ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (g2 v h) (x j) (x i))
        else 0)
        = ∑ j ∈ s, lhs_j j := by
            simp [s, lhs_j, ψ, Finset.sum_filter]
    _ = ∑ j ∈ s, (ℓ ^ 3)⁻¹ * rhs_j j := by
            exact Finset.sum_congr rfl (fun j hj => hpair j hj)
    _ = (ℓ ^ 3)⁻¹ * (∑ j ∈ s, rhs_j j) := by
            rw [Finset.mul_sum]
    _ = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (∑ j ∈ s, aP ℓ j ψ x) * ((aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))) := by
            rw [hswap]
    _ = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (∑ j : Fin (p + 2), if hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
            congr 1
            apply integral_congr_ae
            refine ae_of_all _ (fun x => ?_)
            simp [ψ, s, Finset.sum_filter]
            ring

/-- **L2a at general particle number `N`** (the `(p+2)`-instance lifted by
`N`-cases; the `q2QQ_slot_identity` wrapper pattern). -/
lemma q1_pair_peel_N {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin N) (hij : i ≠ j)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (g2 v h) (x j) (x i))
    = (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
  classical
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      cases n with
      | zero =>
          exfalso
          have hi : i = (0 : Fin 1) := by
            ext
            fin_cases i
            rfl
          have hj : j = (0 : Fin 1) := by
            ext
            fin_cases j
            rfl
          exact hij (hi.trans hj.symm)
      | succ n =>
          simpa using (q1_pair_peel (p := n) hℓ hv_nonneg hvrad hR hv_supp h hRℓ
            (i := i) (j := j) hij hΦc)

/-- **L2c (pairSet total of the q1-word pair part)**: summing the per-pair
peel over the ordered `pairSet N` (`p = (p.1, p.2)`, `i := p.2` the Q-slot,
`j := p.1` the P-slot):

`2·Σ_{p∈pairSet} ∫ (P_{p.1}Q_{p.2}Φ)(P_{p.1}P_{p.2}Φ)·w₂(x p.1)(x p.2)
  = 2·(ℓ³)⁻¹·Σ_{p∈pairSet} ∫ (P_{p.1}Q_{p.2}Φ)(P_{p.2}Φ)·fibre₂(x p.2)`

— the q1-word pair part equals its peeled/sandwich-ready form summed over
the same pairs (each per-pair by `q1_pair_peel_N`). -/
lemma q1_pair_part_total {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * wPairC ℓ (g2 v h) (x p.1) (x p.2))
    = 2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x p.2))) := by
  classical
  have hcongr : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * wPairC ℓ (g2 v h) (x p.1) (x p.2))
      = (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x p.2))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    have hpp := q1_pair_peel_N hℓ hv_nonneg hvrad hR hv_supp h hRℓ
      (i := p.2) (j := p.1) hpij.symm hΦc
    -- hpp : ∫(P_{p.1}Q_{p.2}Φ)(P_{p.1}P_{p.2}Φ)·w₂(x p.1)(x p.2)
    --       = (1/ℓ³)∫(P_{p.1}Q_{p.2}Φ)(P_{p.2}Φ)·fibre₂(x p.2)
    -- goal: the per-p term of the LHS-sum = (1/ℓ³)·(per-p term of RHS-sum) —
    -- hpp's LHS has (aP j(aQ i Φ))·(aP j(aP i Φ))·w₂ with j := p.1, i := p.2:
    -- (aP p.1 (aQ p.2 Φ))·(aP p.1 (aP p.2 Φ))·w₂(x p.1)(x p.2) — matches exactly.
    exact hpp
  calc
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * wPairC ℓ (g2 v h) (x p.1) (x p.2))
        = 2 * ((ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x p.2)))) := by
            rw [hcongr]
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x p.2))) := by ring


/-- **`pairSet` regrouping bridge** (pure Finset): an ordered-distinct-pair sum
reorganised by its second component (the Q-slot `i := p.2`),

`Σ_{p∈pairSet N} f(p.1)(p.2) = Σ_{i : Fin N} Σ_{j≠i} f(j)(i)`,

via the swap-bijection of `univ` + `Finset.sum_product`. -/
lemma pairSet_sum_swap_split {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ p ∈ pairSet N, f p.1 p.2)
      = ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then f j i else 0) := by
  classical
  have h1 : (∑ p ∈ pairSet N, f p.1 p.2)
      = ∑ p : Fin N × Fin N, (if p.1 ≠ p.2 then f p.1 p.2 else 0) := by
    simpa [pairSet] using
      (Finset.sum_filter (s := (Finset.univ : Finset (Fin N × Fin N)))
        (p := fun p : Fin N × Fin N => p.1 ≠ p.2)
        (f := fun p : Fin N × Fin N => f p.1 p.2))
  have hswap : (∑ p : Fin N × Fin N, (if p.1 ≠ p.2 then f p.1 p.2 else 0))
      = ∑ q : Fin N × Fin N, (if q.2 ≠ q.1 then f q.2 q.1 else 0) := by
    refine Finset.sum_bij (s := Finset.univ) (t := Finset.univ)
      (fun p _ => Prod.swap p) ?_ ?_ ?_ ?_
    · intro p hp
      simp
    · intro p hp q hq hpq
      exact Prod.swap_inj.mp hpq
    · intro q hq
      refine ⟨Prod.swap q, by simp, ?_⟩
      simp
    · intro p hp
      simp
  have h2 : (∑ q : Fin N × Fin N, (if q.2 ≠ q.1 then f q.2 q.1 else 0))
      = ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then f j i else 0) := by
    simpa [Finset.univ_product_univ] using
      (Finset.sum_product (s := (Finset.univ : Finset (Fin N)))
        (t := (Finset.univ : Finset (Fin N)))
        (f := fun q : Fin N × Fin N => (if q.2 ≠ q.1 then f q.2 q.1 else 0)))
  calc
    (∑ p ∈ pairSet N, f p.1 p.2)
        = ∑ p : Fin N × Fin N, (if p.1 ≠ p.2 then f p.1 p.2 else 0) := h1
    _ = ∑ q : Fin N × Fin N, (if q.2 ≠ q.1 then f q.2 q.1 else 0) := hswap
    _ = ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then f j i else 0) := h2

/-- **Per-Q-slot sum collapse** (general `N`, the L2a-RHS side): for the
Q-slot `i`, `Σ_{j≠i}∫(P_jQ_iΦ)(P_iΦ)·fibre₂(x_i)` factors into
`∫(P_iΦ)·fibre₂(x_i)·(Σ_{j≠i}P_j(Q_iΦ))` — pure sum-interchange
(`integral_finsetSum` + `Finset.sum_mul`). -/
lemma q1_slot_collapse {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ j : Fin N, if _hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) else 0)
    = ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0) := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter (fun j => j ≠ i)
  have hfint : ∀ j : Fin N, j ∈ s →
      MeasureTheory.Integrable (fun x : X N =>
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))
        (volume.restrict (abox N ℓ)) := by
    intro j hj
    have hji : j ≠ i := by
      simpa [s] using (Finset.mem_filter.mp hj).2
    have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
    have hS : Continuous (fun x : X N => (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)) :=
      (aP_continuous hℓ j hψc).mul (aP_continuous hℓ i hΦc)
    have hFm : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ (g2 v h)) z)
        (volume.restrict (acube ℓ)) := by
      have hfac := fibre_acube_aem (ℓ := ℓ) (h := g2 v h)
        (g2_integrable hR hv_nonneg hvrad hv_supp h)
      simpa [w1Fibre, wPairC] using hfac
    have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
        |w1Fibre ℓ (wPairC ℓ (g2 v h)) z| ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
      intro z hz
      have hb := w2c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
      simpa [w1Fibre, wPairC] using hb
    exact integrableOn_slot_fibre hℓ i hFm hbnd hS
  have hswap : (∑ j ∈ s, (∫ x in abox N ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))))
      = ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x) := by
    calc
      (∑ j ∈ s, (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))))
          = ∫ x in abox N ℓ,
              (∑ j ∈ s, (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
              rw [← integral_finsetSum s hfint]
      _ = ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              change (∑ j ∈ s,
                  aP ℓ j (aQ ℓ i Φ) x * aP ℓ i Φ x * w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))
                  = aP ℓ i Φ x * w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x)
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _hj
              ring
  calc
    (∑ j : Fin N, if hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) else 0)
        = ∑ j ∈ s, (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
            simp [s, Finset.sum_filter]
    _ = ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x) := hswap
    _ = ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (∑ j : Fin N, if hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0) := by
            apply integral_congr_ae
            refine ae_of_all _ (fun x => ?_)
            simp [s, Finset.sum_filter]


/-- **L2c — the q1-word pair part in the per-Q-slot sandwich form** (general
`N`): assembling `q1_pair_part_total` + `pairSet_sum_swap_split` +
`q1_slot_collapse`,

`2·Σ_{p∈pairSet}∫(P_{p.1}Q_{p.2}Φ)(P_{p.1}P_{p.2}Φ)·w₂(x p.1)(x p.2)
  = 2·(ℓ³)⁻¹·Σ_{i:Fin N}∫ (P_iΦ)·fibre₂(x_i)·(Σ_{j≠i}P_j(Q_iΦ))`

— with `Σ_{j≠i}P_jQ_iΦ = Q_i((n₀−P_i)Φ)` (`aP_aQ_comm`) this is the FS
eq:Q1n0 `n₀`-sandwich form of the q1 pair part at every particle number. -/
lemma q1_pair_part_sandwich {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * wPairC ℓ (g2 v h) (x p.1) (x p.2))
    = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
  classical
  have htotal := q1_pair_part_total hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hreg : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x p.2)))
      = ∑ i : Fin N, (∑ j : Fin N, if _hj : j ≠ i then
          (∫ x in abox N ℓ,
            (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
              (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) else 0) := by
    have hsp := pairSet_sum_swap_split (N := N) (f := fun a b : Fin N =>
        ∫ x in abox N ℓ, (aP ℓ a (aQ ℓ b Φ) x) * (aP ℓ b Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x b)))
    simpa [pairSet] using hsp
  have hsum : (∑ i : Fin N, (∑ j : Fin N, if _hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) else 0))
      = ∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact q1_slot_collapse hℓ hv_nonneg hvrad hR hv_supp h hRℓ i hΦc
  calc
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * wPairC ℓ (g2 v h) (x p.1) (x p.2))
        = 2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x p.2))) := htotal
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, (∑ j : Fin N, if _hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) else 0)) := by
            rw [hreg]
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
            rw [hsum]


/-- **`aP` over a finite sum** (pointwise): `P_i` of a `Finset`-sum of
continuous functions is the sum of the `P_i`'s (by induction on the
`Finset`, from `aP_add`). -/
lemma aP_finset_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {ι : Type*} (s : Finset ι)
    {f : ι → X N → ℝ} (hf : ∀ j ∈ s, Continuous (f j)) (x : X N) :
    aP ℓ i (fun y : X N => ∑ j ∈ s, f j y) x = ∑ j ∈ s, aP ℓ i (f j) x := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [aP]
  | insert a s has ih =>
      have hfa : Continuous (f a) := hf a (by simp)
      have hfs : ∀ j ∈ s, Continuous (f j) := by
        intro j hj
        exact hf j (by simp [hj])
      have hIH := ih hfs
      have hfun : (fun y : X N => ∑ j ∈ insert a s, f j y)
          = fun y : X N => f a y + (∑ j ∈ s, f j y) := by
        funext y
        rw [Finset.sum_insert has]
      have hcontS : Continuous (fun y : X N => ∑ j ∈ s, f j y) := by
        exact continuous_finsetSum s (fun j hj => hfs j hj)
      calc
        aP ℓ i (fun y : X N => ∑ j ∈ insert a s, f j y) x
            = aP ℓ i (fun y : X N => f a y + (∑ j ∈ s, f j y)) x := by rw [hfun]
        _ = aP ℓ i (f a) x + aP ℓ i (fun y : X N => ∑ j ∈ s, f j y) x := aP_add hℓ i hfa hcontS x
        _ = aP ℓ i (f a) x + (∑ j ∈ s, aP ℓ i (f j) x) := by rw [hIH]
        _ = ∑ j ∈ insert a s, aP ℓ i (f j) x := by
                rw [Finset.sum_insert has]

/-- **Pointwise `n₀`-collapse (i)**: for the Q-slot `i`,
`Σ_{j≠i} P_j(Q_iΦ) = Q_i((Σ_{j≠i}P_j)Φ)` pointwise (`(n₀−P_i)` acting
inside `Q_i`) — the FS eq:Q1n0 sandwich realisation. -/
lemma q1_n0_collapse {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (x : X N) :
    (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)
    = aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0)) x := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter (fun j => j ≠ i)
  let G : X N → ℝ := fun y => ∑ j ∈ s, aP ℓ j Φ y
  have hcomm : ∀ j : Fin N, j ∈ s → aP ℓ j (aQ ℓ i Φ) x = aQ ℓ i (aP ℓ j Φ) x := by
    intro j hj
    have hji : j ≠ i := by
      simpa [s] using (Finset.mem_filter.mp hj).2
    exact aP_aQ_comm hℓ (i := j) (j := i) hji hΦc x
  have hlin : aP ℓ i G x = ∑ j ∈ s, aP ℓ i (aP ℓ j Φ) x := by
    dsimp [G]
    exact aP_finset_sum hℓ i s (fun j hj => aP_continuous hℓ j hΦc) x
  calc
    (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)
        = ∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x := by simp [s, Finset.sum_filter]
    _ = ∑ j ∈ s, aQ ℓ i (aP ℓ j Φ) x := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hcomm j hj
    _ = ∑ j ∈ s, (aP ℓ j Φ x - aP ℓ i (aP ℓ j Φ) x) := by
            apply Finset.sum_congr rfl
            intro j hj
            rfl
    _ = (∑ j ∈ s, aP ℓ j Φ x) - (∑ j ∈ s, aP ℓ i (aP ℓ j Φ) x) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ j ∈ s, aP ℓ j Φ x) - aP ℓ i G x := by rw [hlin]
    _ = aQ ℓ i G x := by
            change (∑ j ∈ s, aP ℓ j Φ x) - aP ℓ i G x = G x - aP ℓ i G x
            rw [show G x = ∑ j ∈ s, aP ℓ j Φ x by rfl]
    _ = aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0)) x := by
            congr 1
            funext y
            simp [s, G, Finset.sum_filter]


/-- **L2c in the explicit `Q_i((n₀−P_i)Φ)`-form**: `q1_pair_part_sandwich`
with the pointwise `n₀`-collapse (`q1_n0_collapse`) applied per Q-slot:

`2·Σ_{p∈pairSet}∫(P_{p.1}Q_{p.2}Φ)(P_{p.1}P_{p.2}Φ)·w₂(x p.1)(x p.2)
  = 2·(ℓ³)⁻¹·Σ_i∫ (P_iΦ)·fibre₂(x_i)·Q_i((Σ_{j≠i}P_j)Φ)`,

where `(Σ_{j≠i}P_j)Φ = (n₀−P_i)Φ` is the pointwise condensate-field sum
minus the `i`-slot projection. -/
lemma q1_pair_part_sandwich_n0 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * wPairC ℓ (g2 v h) (x p.1) (x p.2))
    = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x) := by
  classical
  have hsand := q1_pair_part_sandwich hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  rw [hsand]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  refine ae_of_all _ (fun x => ?_)
  change aP ℓ i Φ x * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)
      = aP ℓ i Φ x * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x
  have hc := q1_n0_collapse hℓ i hΦc x
  -- hc : Σ_j if j≠i then aP_j(aQ_iΦ) x else 0 = aQ_i(fun y => Σ_j if j≠i then aP_jΦ y else 0) x
  rw [← hc]


/-- **Fibre-additivity of the q1 kernels (ii-1)**: pointwise
`w1Fibre(g₂) z = w1Fibre(g₀) z + w1Fibre(g₀·ω₀) z` — from the pointwise
kernel split `w₂ = w₁ + wPair(g₀ω₀)`
(`FSKernelCompare.wPairC_g2_eq_w1_add_g0w0`) and `integral_add` over the
cube, with the per-`z` fibre integrability from
`KernelMean.kernel_fibre_integrable` (fibre = `χ_ℓ z`-constant multiple of
the `χ_ℓ(y)·wScaled(z−y)`-kernel). -/
lemma w1Fibre_g2_split {ℓ : ℝ} {v : ℝ³ → ℝ} {R : ℝ} (hℓ : 0 < ℓ)
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (z : ℝ³) :
    w1Fibre ℓ (wPairC ℓ (g2 v h)) z
      = w1Fibre ℓ (wPairC ℓ (g0 v h)) z
        + w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z := by
  classical
  let g0w0 : ℝ³ → ℝ := fun w : ℝ³ => g0 v h w * Classical.choose h w
  have hg0w0supp : ∀ y : ℝ³, R ≤ ‖y‖ → g0w0 y = 0 := by
    intro y hy
    have hy0 : g0 v h y = 0 := g0_zero_of_norm_ge hv_supp hy h
    simp [g0w0, hy0]
  have hfib0 : Integrable (fun y : ℝ³ => wPairC ℓ (g0 v h) z y)
      (volume.restrict (acube ℓ)) := by
    have hwi := wScaled_integrable_ae hℓ hR.le hRℓ (g0_integrable hR hv_supp h)
      (fun y hy => g0_zero_of_norm_ge hv_supp hy h)
    have hfib := kernel_fibre_integrable hℓ hwi z
    have hc := hfib.const_mul (chiScale ℓ z)
    have heq : (fun y : ℝ³ => wPairC ℓ (g0 v h) z y)
        = fun y : ℝ³ => chiScale ℓ z * (chiScale ℓ y * wScaled ℓ (g0 v h) (z - y)) := by
      funext y
      simp [wPairC, wPair, mul_comm, mul_left_comm]
    rw [heq]
    exact hc.restrict
  have hfibw0 : Integrable (fun y : ℝ³ => wPairC ℓ g0w0 z y)
      (volume.restrict (acube ℓ)) := by
    have hwi := wScaled_integrable_ae hℓ hR.le hRℓ (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
      (fun y hy => hg0w0supp y hy)
    have hfib := kernel_fibre_integrable hℓ hwi z
    have hc := hfib.const_mul (chiScale ℓ z)
    have heq : (fun y : ℝ³ => wPairC ℓ g0w0 z y)
        = fun y : ℝ³ => chiScale ℓ z * (chiScale ℓ y * wScaled ℓ g0w0 (z - y)) := by
      funext y
      simp [wPairC, wPair, mul_comm, mul_left_comm]
    rw [heq]
    exact hc.restrict
  calc
    (∫ y in acube ℓ, wPairC ℓ (g2 v h) z y)
        = ∫ y in acube ℓ,
            (wPairC ℓ (g0 v h) z y + wPairC ℓ g0w0 z y) := by
            apply integral_congr_ae
            refine ae_of_all _ (fun y => ?_)
            have hsp := wPairC_g2_eq_w1_add_g0w0 (ℓ := ℓ) (v := v) h z y
            simpa [g0w0] using hsp
    _ = (∫ y in acube ℓ, wPairC ℓ (g0 v h) z y)
        + (∫ y in acube ℓ, wPairC ℓ g0w0 z y) := by
            rw [integral_add hfib0 hfibw0]


/-- **q1word in the `n₀`-sandwich + one-body form (ii-2a)**: with
`w₁ := wPairC(g0)`, `w₂ := wPairC(g2)`, `f₂(z) := w1Fibre(wPairC(g2)) z`,

`q1word(N,ℓ,μ,w₁,w₂)Φ
  = 2(ℓ³)⁻¹·Σ_i∫ (P_iΦ)·f₂(x_i)·Q_i((Σ_{j≠i}P_j)Φ)
    − 2μ·Σ_i∫ (Q_iΦ)(P_iΦ)·f₁(x_i)`

(`f₁(z) := w1Fibre(wPairC(g0)) z`) — q1word's pair part via
`q1_pair_part_sandwich_n0`, its own one-body term unchanged. -/
lemma q1word_eq_sandwich_f2 {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
    = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))) := by
  classical
  have hsand := q1_pair_part_sandwich_n0 hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  unfold q1word
  rw [hsand]


/-- Fibre bound of the `w₁ω`-kernel (`g₀·ω₀`-numerator):
`|w1Fibre(wPairC(g₀ω₀)) z| ≤ chiSup²·2·(8π·a v)` for `z` in the cube
(clone of `PotChosen.w1c_fibre_acube_abs_le` with `h := g₀ω₀`, using
`∫g₀ω₀ ≤ 8πa`). -/
lemma w1c_g0w0_fibre_acube_abs_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |∫ y in acube ℓ, wPair ℓ (fun z : ℝ³ => g0 v h z * Classical.choose h z) x y|
      ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
  let g0w0 : ℝ³ → ℝ := fun z : ℝ³ => g0 v h z * Classical.choose h z
  have hbnd := fibre_acube_abs_le (h := g0w0) hℓ (le_of_lt hR) hRℓ
    (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
    (fun z hz => by
      have hz0 : g0 v h z = 0 := g0_zero_of_norm_ge hv_supp hz h
      simp [g0w0, hz0]) x
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ g0w0 z := by
    dsimp [g0w0]
    have hg0 : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
    have hw0 : ∀ᵐ z : ℝ³, 0 ≤ Classical.choose h z :=
      (scattering_bounds_ae hR hv_nonneg hvrad hv_supp (w0_spec h).1 (w0_spec h).2).1
    filter_upwards [hg0, hw0] with z hz0 hw
    exact mul_nonneg hz0 hw
  have hEq : (∫ z : ℝ³, |g0w0 z|) = ∫ z : ℝ³, g0w0 z := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  have hleInt : (∫ z : ℝ³, g0w0 z) ≤ 8 * π * a v := by
    have hb := chosen_gomega_integral_bounds hR hv_nonneg hvrad hv_supp h
    simpa [g0w0, g0] using hb.2
  have hnnC : 0 ≤ chiSup ^ 2 * 2 := by positivity
  calc
    |∫ y in acube ℓ, wPair ℓ g0w0 x y| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |g0w0 z|) := hbnd
    _ = chiSup ^ 2 * 2 * (∫ z : ℝ³, g0w0 z) := by rw [hEq]
    _ ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
        exact mul_le_mul_of_nonneg_left hleInt hnnC

/-- **q1word's eq:Q1n0 two-line form (ii-2)**: with `f₁(z) :=
w1Fibre(wPairC(g0)) z`, `f₁ω(z) := w1Fibre(wPairC(g₀ω₀)) z`,

`q1word(N,ℓ,μ,w₁,w₂)Φ
  = 2(ℓ³)⁻¹·Σ_i∫(P_iΦ)·f₁(x_i)·Q_i((Σ_{j≠i}P_j)Φ)
    + 2(ℓ³)⁻¹·Σ_i∫(P_iΦ)·f₁ω(x_i)·Q_i((Σ_{j≠i}P_j)Φ)
    − 2μ·Σ_i∫(Q_iΦ)(P_iΦ)·f₁(x_i)`

— the w₁-line (combining with the −2μ-onebody into FS's `((n₀/V)−μ)`-form)
and the w₁ω-line (Step-2's PPQω-cancellation partner). -/
lemma q1word_eq_q1n0_split {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
    = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      + 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))) := by
  classical
  let f1 : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g0 v h)) z
  let f1w : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z
  let f2 : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g2 v h)) z
  have hF1m : AEStronglyMeasurable f1 (volume.restrict (acube ℓ)) := by
    dsimp [f1]
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hC1 : ∀ z : ℝ³, z ∈ acube ℓ → |f1 z| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
    intro z hz
    dsimp [f1]
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  have hF1wm : AEStronglyMeasurable f1w (volume.restrict (acube ℓ)) := by
    dsimp [f1w]
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := fun w : ℝ³ => g0 v h w * Classical.choose h w)
      (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hC1w : ∀ z : ℝ³, z ∈ acube ℓ → |f1w z| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
    intro z hz
    dsimp [f1w]
    have hb := w1c_g0w0_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  have hmain := q1word_eq_sandwich_f2 (μ := μ) hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  -- per-i split of the f₂-sandwich integrand
  have hper : ∀ i : Fin N,
      (∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (f2 (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      = (∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (f1 (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
        + (∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (f1w (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x) := by
    intro i
    let G : X N → ℝ := fun y => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0)
    have hGc : Continuous G := by
      dsimp [G]
      refine continuous_finsetSum (Finset.univ) ?_
      intro j hj
      by_cases hji : j ≠ i
      · have hc := aP_continuous hℓ j hΦc
        simpa [hji] using hc
      · simpa [hji] using (continuous_const : Continuous (fun _ : X N => (0 : ℝ)))
    have hQiGc : Continuous (fun x : X N => aQ ℓ i G x) := by
      change Continuous (fun x : X N => G x - aP ℓ i G x)
      exact hGc.sub (aP_continuous hℓ i hGc)
    have hS : Continuous (fun x : X N => (aP ℓ i Φ x) * (aQ ℓ i G x)) :=
      (aP_continuous hℓ i hΦc).mul hQiGc
    have hint1 : IntegrableOn (fun x : X N => (aP ℓ i Φ x) * (f1 (x i)) * (aQ ℓ i G x))
        (abox N ℓ) volume := by
      have h1 := integrableOn_slot_fibre hℓ i hF1m hC1 hS
      simpa [mul_assoc, mul_left_comm, mul_comm] using h1
    have hint1w : IntegrableOn (fun x : X N => (aP ℓ i Φ x) * (f1w (x i)) * (aQ ℓ i G x))
        (abox N ℓ) volume := by
      have h1 := integrableOn_slot_fibre hℓ i hF1wm hC1w hS
      simpa [mul_assoc, mul_left_comm, mul_comm] using h1
    calc
      (∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (f2 (x i)) * (aQ ℓ i G x))
          = ∫ x in abox N ℓ,
              (aP ℓ i Φ x) * (f1 (x i) + f1w (x i)) * (aQ ℓ i G x) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              have hz := w1Fibre_g2_split hℓ hR hv_nonneg hvrad hv_supp h hRℓ (x i)
              dsimp [f1, f1w, f2]
              rw [hz]
      _ = ∫ x in abox N ℓ,
              (aP ℓ i Φ x) * (f1 (x i)) * (aQ ℓ i G x)
              + (aP ℓ i Φ x) * (f1w (x i)) * (aQ ℓ i G x) := by
              have hfun : (fun x : X N => (aP ℓ i Φ x) * (f1 (x i) + f1w (x i)) * (aQ ℓ i G x))
                  = fun x : X N => (aP ℓ i Φ x) * (f1 (x i)) * (aQ ℓ i G x)
                      + (aP ℓ i Φ x) * (f1w (x i)) * (aQ ℓ i G x) := by
                funext x
                ring
              rw [hfun]
      _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) * (f1 (x i)) * (aQ ℓ i G x))
          + (∫ x in abox N ℓ, (aP ℓ i Φ x) * (f1w (x i)) * (aQ ℓ i G x)) := by
              rw [integral_add hint1 hint1w]
  -- reassemble
  have hSsum : (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (f2 (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      = (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (f1 (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
        + (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (f1w (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hper i
  rw [hmain]
  rw [hSsum]
  ring


/-! ## PPQω-cancellation atoms — the `w₁ω := wPairC(g₀·ω₀)`-kernel layer

The FS Q3+Q4CS leftover (`−Σ(P_iQ_jw₁ωP_jP_i+h.c.)`) cancels the eq:Q1n0
w₁ω-line exactly; formally the q1-pair-sum with the `w₁ω`-kernel collapses
to the w₁ω-sandwich (clone of the `w₂`-machinery for the numerator
`g₀·ω₀`).  The atoms below provide the `g₀ω₀`-kernel instances of
evenness, fibre symmetry and the per-pair integrability. -/

/-- `g₀·ω₀` is even (`g0_even` + radiality of `ω₀`). -/
lemma g0w0_even {v : ℝ³ → ℝ} (hvrad : IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ z : ℝ³, (fun w : ℝ³ => g0 v h w * Classical.choose h w) (-z)
        = (fun w : ℝ³ => g0 v h w * Classical.choose h w) z := by
  have hrad₀ : IsRadial (Classical.choose h) := (w0_spec h).1
  intro x
  have hg := g0_even hvrad h x
  have hw := radial_neg hrad₀ x
  simp [hg, hw]

/-- First-slot fibre of the symmetric `w₁ω`-kernel equals its `w1Fibre`
(clone of `FibreLocal.w2_fibre_first_slot_eq` for `h := g₀ω₀`). -/
lemma g0w0_fibre_first_slot_eq {ℓ : ℝ} {v : ℝ³ → ℝ} (hvrad : IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (z : ℝ³) :
    (∫ y in acube ℓ, wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) y z)
      = w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z := by
  calc
    (∫ y in acube ℓ, wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) y z)
        = ∫ y in acube ℓ, wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) z y := by
            apply integral_congr_ae
            refine ae_of_all _ (fun y => ?_)
            change wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) y z
                = wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) z y
            exact wPairC_sym (g0w0_even hvrad h) ℓ y z
    _ = w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z := by
            simp [w1Fibre, wPairC]

/-- Integrability over `abox (p+2) ℓ` of the q1-pair LHS integrand with the
`w₁ω`-kernel (`q1F_int` clone, numerator `g₀·ω₀`). -/
lemma q1Fw0_int {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j) (x i))
      (abox (p + 2) ℓ) volume := by
  classical
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hPψc : Continuous (fun x : X (p + 2) => aP ℓ j (aQ ℓ i Φ) x) :=
    aP_continuous hℓ j hψc
  have hPc : Continuous (fun x : X (p + 2) => aP ℓ j (aP ℓ i Φ) x) :=
    aP_continuous hℓ j (aP_continuous hℓ i hΦc)
  have hSc : Continuous (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) := hPψc.mul hPc
  obtain ⟨B, hB⟩ := (abox_compact (p + 2) hℓ).exists_bound_of_continuousOn
    (s := abox (p + 2) ℓ)
    (f := fun x : X (p + 2) => (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x))
    hSc.continuousOn
  have hw2i : IntegrableOn (wPairU ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w))
      (acube ℓ ×ˢ acube ℓ) volume := by
    have hi := g0w0_integrable hR hv_nonneg hvrad hv_supp h
    have hsupp : ∀ z : ℝ³, R ≤ ‖z‖ →
        (fun w : ℝ³ => g0 v h w * Classical.choose h w) z = 0 := by
      intro z hz
      have hz0 : g0 v h z = 0 := g0_zero_of_norm_ge hv_supp hz h
      simp [hz0]
    exact integrableOn_wPairU_of hℓ hi hsupp (le_of_lt hR) hRℓ
  have hwcomp : IntegrableOn (fun x : X (p + 2) =>
      wPairU ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j, x i))
      (abox (p + 2) ℓ) volume :=
    integrableOn_pair_comp_ae hℓ j i hij.symm hw2i
  have hwabs : Integrable (fun x : X (p + 2) =>
      |wPairU ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j, x i)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    have hwabs' := hwcomp.abs
    simpa [Real.norm_eq_abs] using hwabs'
  have hbnd : ∀ᵐ x ∂(volume.restrict (abox (p + 2) ℓ)),
      ‖((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) *
          wPairU ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j, x i)‖
        ≤ B * |wPairU ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j, x i)| := by
    rw [ae_restrict_iff' (abox_measurable (p + 2) ℓ)]
    apply ae_of_all
    intro x hx
    have hle : |(aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)| ≤ B := by
      have hb' := hB x hx
      simpa [Real.norm_eq_abs] using hb'
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hmeas : AEStronglyMeasurable (fun x : X (p + 2) =>
      ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) *
          wPairU ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j, x i))
      (volume.restrict (abox (p + 2) ℓ)) := by
    exact hSc.aestronglyMeasurable.mul hwcomp.aestronglyMeasurable
  have hdomin : Integrable (fun x : X (p + 2) =>
      B * |wPairU ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j, x i)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    exact hwabs.const_mul B
  have hgoal : Integrable (fun x : X (p + 2) =>
      ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) *
          wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j) (x i))
      (volume.restrict (abox (p + 2) ℓ)) := by
    change Integrable (fun x : X (p + 2) =>
        ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) *
          wPairU ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j, x i))
      (volume.restrict (abox (p + 2) ℓ))
    exact Integrable.mono' hdomin hmeas hbnd
  exact hgoal

/-- Integrability over `abox (p+2) ℓ` of the q1-pair RHS integrand with the
`f₁ω`-fibre (`q1G_int` clone). -/
lemma q1Gw0_int {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (_hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)))
      (abox (p + 2) ℓ) volume := by
  classical
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hS : Continuous (fun x : X (p + 2) => (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)) :=
    (aP_continuous hℓ j hψc).mul (aP_continuous hℓ i hΦc)
  have hFm : AEStronglyMeasurable (fun z : ℝ³ =>
      w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z)
      (volume.restrict (acube ℓ)) := by
    have hfac := fibre_acube_aem (ℓ := ℓ)
      (h := fun w : ℝ³ => g0 v h w * Classical.choose h w)
      (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
      |w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z|
        ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
    intro z hz
    have hb := w1c_g0w0_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  exact integrableOn_slot_fibre hℓ i hFm hbnd hS


lemma q1_lhs_closed_w0 {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j) (x i))
    = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) := by
  classical
  let F : X (p + 2) → ℝ := fun x =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j) (x i)
  let G : X (p + 2) → ℝ := fun x =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))
  have hF : IntegrableOn F (abox (p + 2) ℓ) volume := by
    simpa [F] using (q1Fw0_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc)
  have hG : IntegrableOn G (abox (p + 2) ℓ) volume := by
    classical
    have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
    have hS : Continuous (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j hψc).mul (aP_continuous hℓ j (aP_continuous hℓ i hΦc))
    have hFm : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z)
        (volume.restrict (acube ℓ)) := by
      have hfac := fibre_acube_aem (ℓ := ℓ)
        (h := fun w : ℝ³ => g0 v h w * Classical.choose h w)
        (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
      simpa [w1Fibre, wPairC] using hfac
    have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
        |w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z|
          ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
      intro z hz
      have hb := w1c_g0w0_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
      simpa [w1Fibre, wPairC] using hb
    have hInt := integrableOn_slot_fibre hℓ i hFm hbnd hS
    simpa [G] using hInt
  have hpeelF : (∫ x in abox (p + 2) ℓ, F x)
      = ∫ r : X (p + 1), (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) :=
      abox_integral_peel (n := p + 1) (i := j) (F := F) hF
  have hpeelG : (∫ x in abox (p + 2) ℓ, G x)
      = ∫ r : X (p + 1), (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) :=
      abox_integral_peel (n := p + 1) (i := j) (F := G) hG
  have hci : ∀ (r : X (p + 1)) (y : ℝ³),
      (kcInsN (p + 1) j (y, r)) i = (kcInsN (p + 1) j (0, r)) i := by
    intro r y
    exact kc_insN_other_indep (p + 1) j y 0 r i hij
  have hinner : ∀ r : X (p + 1),
      (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
        = (ℓ ^ 3)⁻¹ * (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r))) := by
    intro r
    let ci : ℝ³ := (kcInsN (p + 1) j (0, r)) i
    let CA : ℝ := (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, (aQ ℓ i Φ) (kcInsN (p + 1) j (z, r)))
    let CB : ℝ := (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, (aP ℓ i Φ) (kcInsN (p + 1) j (z, r)))
    have hFibre : (∫ y in acube ℓ, wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) y ci) = w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) ci :=
      g0w0_fibre_first_slot_eq hvrad h ci
    have hAcst : ∀ y : ℝ³, aP ℓ j (aQ ℓ i Φ) (kcInsN (p + 1) j (y, r)) = CA := by
      intro y
      dsimp [CA]
      simpa using (aP_kcInsN (ℓ := ℓ) (i := j) (Φ := aQ ℓ i Φ) y r)
    have hBcst : ∀ y : ℝ³, aP ℓ j (aP ℓ i Φ) (kcInsN (p + 1) j (y, r)) = CB := by
      intro y
      dsimp [CB]
      simpa using (aP_kcInsN (ℓ := ℓ) (i := j) (Φ := aP ℓ i Φ) y r)
    have hFy : (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
        = CA * CB * w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) ci := by
      calc
        (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
            = ∫ y in acube ℓ,
                (aP ℓ j (aQ ℓ i Φ) (kcInsN (p + 1) j (y, r))) *
                  (aP ℓ j (aP ℓ i Φ) (kcInsN (p + 1) j (y, r))) *
                  wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (kcInsN (p + 1) j (y, r) j) (kcInsN (p + 1) j (y, r) i) := by
                dsimp [F]
        _ = ∫ y in acube ℓ, CA * CB * wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) y ci := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                dsimp [F]
                have hyj : (kcInsN (p + 1) j (y, r)) j = y := kc_insN_apply_same (p + 1) j y r
                rw [hAcst y, hBcst y, hyj, hci r y]
        _ = CA * CB * (∫ y in acube ℓ, wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) y ci) := by
                rw [integral_const_mul]
        _ = CA * CB * w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) ci := by
                rw [← hFibre]
                simp [wPairC]
    have hGy : (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
        = (ℓ ^ 3) * CA * CB * w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) ci := by
      calc
        (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
            = ∫ y in acube ℓ,
                (aP ℓ j (aQ ℓ i Φ) (kcInsN (p + 1) j (y, r))) *
                  (aP ℓ j (aP ℓ i Φ) (kcInsN (p + 1) j (y, r))) *
                  (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (kcInsN (p + 1) j (y, r) i)) := by
                dsimp [G]
        _ = ∫ y in acube ℓ, CA * CB * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) ci) := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                dsimp [G]
                rw [hAcst y, hBcst y, hci r y]
        _ = (ℓ ^ 3) * CA * CB * w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) ci := by
                rw [integral_const_acube ℓ hℓ (CA * CB * w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) ci)]
                ring
    rw [hFy, hGy]
    field_simp [ne_of_gt hℓ]
  calc
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j) (x i))
        = ∫ x in abox (p + 2) ℓ, F x := by
            simp [F]
    _ = ∫ r : X (p + 1), (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := hpeelF
    _ = ∫ r : X (p + 1), (ℓ ^ 3)⁻¹ * (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := by
            apply integral_congr_ae
            refine ae_of_all _ (fun r => ?_)
            exact hinner r
    _ = (ℓ ^ 3)⁻¹ * ∫ r : X (p + 1), (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := by
            rw [integral_const_mul]
    _ = (ℓ ^ 3)⁻¹ * ∫ x in abox (p + 2) ℓ, G x := by
            rw [hpeelG]
    _ = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) := by
            simp [G]



lemma q1_pair_replace_w0 {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)))
    = (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) := by
  classical
  let w : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z
  have hFm : AEStronglyMeasurable w (volume.restrict (acube ℓ)) := by
    dsimp [w]
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := fun w : ℝ³ => g0 v h w * Classical.choose h w)
      (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hC : ∀ z : ℝ³, z ∈ acube ℓ → |w z| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
    intro z hz
    dsimp [w]
    have hb := w1c_g0w0_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  have hortho := q1_ortho hℓ hij (w := w) (C := chiSup ^ 2 * 2 * (8 * π * a v)) hFm hC hΦc
  have hBpt : ∀ x : X (p + 2),
      aP ℓ j (aP ℓ i Φ) x - aP ℓ i Φ x = - (aP ℓ i (aQ ℓ j Φ) x) := by
    intro x
    have hPjc : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
    have hcomm := aP_comm hℓ j i hΦc x
    have hsub := aP_sub hℓ i (Φ := Φ) (Ψ := aP ℓ j Φ) hΦc hPjc x
    have hA : aQ ℓ j Φ = Φ - aP ℓ j Φ := by funext y; rfl
    calc
      aP ℓ j (aP ℓ i Φ) x - aP ℓ i Φ x
          = aP ℓ i (aP ℓ j Φ) x - aP ℓ i Φ x := by rw [hcomm]
      _ = - (aP ℓ i Φ x - aP ℓ i (aP ℓ j Φ) x) := by ring
      _ = - (aP ℓ i (aQ ℓ j Φ) x) := by
              rw [hA]
              rw [← aP_sub hℓ i hΦc hPjc x]
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hS1 : Continuous (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)) :=
    (aP_continuous hℓ j hψc).mul (aP_continuous hℓ j (aP_continuous hℓ i hΦc))
  have hIntAB : IntegrableOn (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * (w (x i)))
      (abox (p + 2) ℓ) volume := by
    have h1 := integrableOn_slot_fibre hℓ i hFm hC hS1
    simpa [w] using h1
  have hIntAP : IntegrableOn (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w (x i)))
      (abox (p + 2) ℓ) volume := by
    have h1 := q1Gw0_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc
    simpa [w] using h1
  have hdiff : (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * (w (x i)))
      - (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w (x i))) = 0 := by
    have hsub := integral_sub hIntAB hIntAP
    -- hsub : ∫AB·w − ∫AP·w = ∫(AB·w − AP·w)
    have hbody : (fun x : X (p + 2) =>
          ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) - (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)) * (w (x i)))
        = fun x : X (p + 2) =>
          - ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * (w (x i))) := by
      funext x
      have hB := hBpt x
      have hfac : (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x)
            - (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)
          = (aP ℓ j (aQ ℓ i Φ) x) * ((aP ℓ j (aP ℓ i Φ) x) - (aP ℓ i Φ x)) := by ring
      rw [hfac, hB]
      ring
    calc
      (∫ x in abox (p + 2) ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * (w (x i)))
          - (∫ x in abox (p + 2) ℓ,
              (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w (x i)))
          = ∫ x in abox (p + 2) ℓ,
              ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * (w (x i)))
              - ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w (x i))) := hsub.symm
      _ = ∫ x in abox (p + 2) ℓ,
              ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) - (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)) * (w (x i)) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              ring
      _ = ∫ x in abox (p + 2) ℓ,
          - ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * (w (x i))) := by
              rw [hbody]
      _ = 0 := by
              have hneg : (∫ x in abox (p + 2) ℓ,
                  - ((aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * (w (x i))))
                  = - (∫ x in abox (p + 2) ℓ,
                      (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * (w (x i))) := by
                    rw [integral_neg]
              rw [hneg]
              rw [hortho]
              ring
  have hgoal : (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)))
      = (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) := by
    simpa [w] using (sub_eq_zero.mp hdiff)
  exact hgoal

lemma q1_pair_peel_w0 {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j) (x i))
    = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) := by
  classical
  have hpeel := q1_lhs_closed_w0 hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc
  have hrep := q1_pair_replace_w0 hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc
  rw [hpeel]
  rw [hrep]



lemma q1_pair_peel_w0_N {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin N) (hij : i ≠ j)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x j) (x i))
    = (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) := by
  classical
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      cases n with
      | zero =>
          exfalso
          have hi : i = (0 : Fin 1) := by
            ext
            fin_cases i
            rfl
          have hj : j = (0 : Fin 1) := by
            ext
            fin_cases j
            rfl
          exact hij (hi.trans hj.symm)
      | succ n =>
          simpa using (q1_pair_peel_w0 (p := n) hℓ hv_nonneg hvrad hR hv_supp h hRℓ
            (i := i) (j := j) hij hΦc)

lemma q1_pair_part_total_w0 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
    = 2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x p.2))) := by
  classical
  have hcongr : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      = (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x p.2))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    have hpp := q1_pair_peel_w0_N hℓ hv_nonneg hvrad hR hv_supp h hRℓ
      (i := p.2) (j := p.1) hpij.symm hΦc
    -- hpp : ∫(P_{p.1}Q_{p.2}Φ)(P_{p.1}P_{p.2}Φ)·w₂(x p.1)(x p.2)
    --       = (1/ℓ³)∫(P_{p.1}Q_{p.2}Φ)(P_{p.2}Φ)·fibre₂(x p.2)
    -- goal: the per-p term of the LHS-sum = (1/ℓ³)·(per-p term of RHS-sum) —
    -- hpp's LHS has (aP j(aQ i Φ))·(aP j(aP i Φ))·w₂ with j := p.1, i := p.2:
    -- (aP p.1 (aQ p.2 Φ))·(aP p.1 (aP p.2 Φ))·w₂(x p.1)(x p.2) — matches exactly.
    exact hpp
  calc
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        = 2 * ((ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x p.2)))) := by
            rw [hcongr]
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x p.2))) := by ring



lemma q1_slot_collapse_w0 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ j : Fin N, if _hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) else 0)
    = ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
          (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0) := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter (fun j => j ≠ i)
  have hfint : ∀ j : Fin N, j ∈ s →
      MeasureTheory.Integrable (fun x : X N =>
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)))
        (volume.restrict (abox N ℓ)) := by
    intro j hj
    have hji : j ≠ i := by
      simpa [s] using (Finset.mem_filter.mp hj).2
    have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
    have hS : Continuous (fun x : X N => (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x)) :=
      (aP_continuous hℓ j hψc).mul (aP_continuous hℓ i hΦc)
    have hFm : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z)
        (volume.restrict (acube ℓ)) := by
      have hfac := fibre_acube_aem (ℓ := ℓ) (h := fun w : ℝ³ => g0 v h w * Classical.choose h w)
        (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
      simpa [w1Fibre, wPairC] using hfac
    have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
        |w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) z|
          ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
      intro z hz
      have hb := w1c_g0w0_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
      simpa [w1Fibre, wPairC] using hb
    exact integrableOn_slot_fibre hℓ i hFm hbnd hS
  have hswap : (∑ j ∈ s, (∫ x in abox N ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))))
      = ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x) := by
    calc
      (∑ j ∈ s, (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))))
          = ∫ x in abox N ℓ,
              (∑ j ∈ s, (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) := by
              rw [← integral_finsetSum s hfint]
      _ = ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              change (∑ j ∈ s,
                  aP ℓ j (aQ ℓ i Φ) x * aP ℓ i Φ x * w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))
                  = aP ℓ i Φ x * w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x)
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _hj
              ring
  calc
    (∑ j : Fin N, if hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) else 0)
        = ∑ j ∈ s, (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) := by
            simp [s, Finset.sum_filter]
    _ = ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x) := hswap
    _ = ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
          (∑ j : Fin N, if hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0) := by
            apply integral_congr_ae
            refine ae_of_all _ (fun x => ?_)
            simp [s, Finset.sum_filter]


/-- **PPQω-cancellation — the `w₁ω`-sandwich identity (Step-2 leftover
partner)**: the q1-pair-sum with the `w₁ω := wPairC(g₀·ω₀)`-kernel (the
corpus avatar of the Q3+Q4CS leftover `−Σ(P_iQ_jw₁ωP_jP_i+h.c.)`) collapses,
at every particle number, to the w₁ω-line of `q1word_eq_q1n0_split`:

`2·Σ_{p∈pairSet}∫(P_{p.1}Q_{p.2}Φ)(P_{p.1}P_{p.2}Φ)·w₁ω(x p.1)(x p.2)
  = 2·(ℓ³)⁻¹·Σ_i∫ (P_iΦ)·f₁ω(x_i)·(Σ_{j≠i}P_j(Q_iΦ))`

(`f₁ω := w1Fibre(w₁ω)`), i.e. the Q3+Q4CS w₁ω-leftover is the exact
negative partner of eq:Q1n0's w₁ω-line — the cancellation that leaves only
the `(n₀/V−μ)`-w₁-line (Step 4's CS input) and the `n₊`-masses. -/
lemma q1_pair_part_sandwich_w0 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
          wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
    = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
          (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
  classical
  have htotal := q1_pair_part_total_w0 hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hreg : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x p.2)))
      = ∑ i : Fin N, (∑ j : Fin N, if _hj : j ≠ i then
          (∫ x in abox N ℓ,
            (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
              (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) else 0) := by
    have hsp := pairSet_sum_swap_split (N := N) (f := fun a b : Fin N =>
        ∫ x in abox N ℓ, (aP ℓ a (aQ ℓ b Φ) x) * (aP ℓ b Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x b)))
    simpa [pairSet] using hsp
  have hsum : (∑ i : Fin N, (∑ j : Fin N, if _hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) else 0))
      = ∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact q1_slot_collapse_w0 hℓ hv_nonneg hvrad hR hv_supp h hRℓ i hΦc
  calc
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
          wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        = 2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x p.2))) := htotal
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, (∑ j : Fin N, if _hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i))) else 0)) := by
            rw [hreg]
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
          (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
            rw [hsum]


/-- **S2 summation (row 5)**: `q2PairWord` equals the peeled slot-sandwich
sum — summing the (closed) per-slot identity
`Q2Mass.q2QQ_slot_identity` over the Q-slots after reindexing the
`pairSet`-sum by its second component:

    q2PairWord(Φ) = (1/ℓ³)·Σ_i ∫ (Q_iΦ)·fibre₂(x_i)·(Σ_{j≠i}P_j(Q_iΦ))

(`fibre₂ := w1Fibre ℓ (wPairC ℓ (g2 v h))`; the `Σ_{j≠i}P_j(Q_iΦ)`-factor
kept as the pointwise operator sum — the n₀-realised sandwich of FS
eq:Q2n0's `+ρ₀`-half, exactly the `q2QQ_slot_identity_statement` design
target).  Square-rewrite of the q2PairWord integrand via `aP_aQ_comm`
(`Q_jP_i = P_iQ_j`), reindex `pairSet_sum_swap_split`, then per-slot
`q2QQ_slot_identity`. -/
lemma q2PairWord_eq_slot_sandwich {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      = (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
  classical
  have hsq : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpij : p.1 ≠ p.2 := by simpa [pairSet] using (Finset.mem_filter.mp hp).2
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    change aP ℓ p.1 (aQ ℓ p.2 Φ) x * aQ ℓ p.2 (aP ℓ p.1 Φ) x * wPairC ℓ (g2 v h) (x p.1) (x p.2)
        = (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)
    rw [← aP_aQ_comm hℓ hpij hΦc x]
    ring
  have hre : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2))
      = ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
          (∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i)) else 0) := by
    have hsp := pairSet_sum_swap_split (N := N) (f := fun a b : Fin N =>
        ∫ x in abox N ℓ, (aP ℓ a (aQ ℓ b Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x a) (x b))
    simpa using hsp
  have hsum : (∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
        (∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i)) else 0))
      = ∑ i : Fin N, (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact q2QQ_slot_identity hℓ hv_nonneg hvrad hR hv_supp h hRℓ i hΦc
  calc
    q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
        = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
              wPairC ℓ (g2 v h) (x p.1) (x p.2) := rfl
    _ = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2) := hsq
    _ = ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
        (∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i)) else 0) := hre
    _ = ∑ i : Fin N, (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := hsum
    _ = (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
            rw [Finset.mul_sum]

end BoseGases

end Submission