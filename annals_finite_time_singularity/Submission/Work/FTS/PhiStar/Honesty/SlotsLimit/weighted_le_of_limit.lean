import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.exists_subseq_ae_tendsto
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrable_sq_mul_le_of_tendsto_ae
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.tendsto_sq_sub_of_cauchy_of_ae
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.cs_limit_tendsto
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.integrable_mul_of_sq
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.integrable_mul_of_sq_sub_bounded
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.integrable_sq_mul_sub
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.locallyIntegrableOn_sub
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.test_mul_continuousOn
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.test_weight_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory Set Filter
open scoped Real Topology

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ### A name-resolution workaround for the statement below

The statement of `weighted_le_of_limit` (fixed by the requester) writes the at-top filter on `ℕ` as
the *doubly* qualified name `Filter.Filter.atTop`, which is not a Mathlib constant.  To keep that
statement textually unchanged while making it elaborate, we introduce
`Filter.Filter.atTop` as an alias of the standard `Filter.atTop` on `ℕ` (the alias is a plain
`def`, so it adds no axiom and changes no statement: the two filters are equal by `rfl`). -/

/-- Alias of the standard at-top filter on `ℕ`, under the doubly qualified name used by the
statement of `weighted_le_of_limit`. -/
noncomputable def ftsNatAtTop : Filter ℕ := Filter.atTop

noncomputable def _root_.Filter.Filter.atTop : Filter ℕ := ftsNatAtTop

/-! ### Conversion helpers for the unweighted (`w ≡ 1`) Cauchy–Schwarz limit passage

The limit passage `WeightedLimitAux.cs_limit_tendsto` is stated for a general *weight* `w`; in the
unweighted instance `w ≡ 1` its hypotheses take the shapes `AEStronglyMeasurable (f · * 1)` and
`Integrable (fun x => (h x / 1) ^ 2)` (and its limit hypothesis involves `(f · * 1) ^ 2`).  The
following lemmas convert to and from those shapes. -/

private theorem aesm_mul_one {F : ℝ × ℝ → ℝ}
    (h : AEStronglyMeasurable F (volume.restrict Q0)) :
    AEStronglyMeasurable (fun x => F x * (1 : ℝ)) (volume.restrict Q0) := by
  have h1 : (fun x : ℝ × ℝ => F x * 1) = F := by funext x; simp only [mul_one]
  rw [h1]; exact h

private theorem aesm_div_one {F : ℝ × ℝ → ℝ}
    (h : AEStronglyMeasurable F (volume.restrict Q0)) :
    AEStronglyMeasurable (fun x => F x / (1 : ℝ)) (volume.restrict Q0) := by
  have h1 : (fun x : ℝ × ℝ => F x / 1) = F := by funext x; simp only [div_one]
  rw [h1]; exact h

private theorem int_sq_mul_one {F : ℝ × ℝ → ℝ}
    (h : Integrable (fun x => F x ^ 2) (volume.restrict Q0)) :
    Integrable (fun x => (F x * (1 : ℝ)) ^ 2) (volume.restrict Q0) :=
  h.congr (Filter.Eventually.of_forall fun x => by simp only [mul_one])

private theorem int_sq_div_one {F : ℝ × ℝ → ℝ}
    (h : Integrable (fun x => F x ^ 2) (volume.restrict Q0)) :
    Integrable (fun x => (F x / (1 : ℝ)) ^ 2) (volume.restrict Q0) :=
  h.congr (Filter.Eventually.of_forall fun x => by simp only [div_one])

/-- The **unweighted** Cauchy–Schwarz limit passage: if `∫ (f k)² → 0` and `h ∈ L²`, then
`∫ f k · h → 0`.  (Instance of `WeightedLimitAux.cs_limit_tendsto` at the weight `w ≡ 1`.) -/
private theorem cs_limit_unweighted {f : ℕ → ℝ × ℝ → ℝ} {h : ℝ × ℝ → ℝ}
    (hA : ∀ k, AEStronglyMeasurable (f k) (volume.restrict Q0))
    (hB : AEStronglyMeasurable h (volume.restrict Q0))
    (hAint : ∀ k, Integrable (fun x => f k x ^ 2) (volume.restrict Q0))
    (hBint : Integrable (fun x => h x ^ 2) (volume.restrict Q0))
    (hlim : Tendsto (fun k => ∫ x, f k x ^ 2 ∂(volume.restrict Q0)) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x, f k x * h x ∂(volume.restrict Q0)) atTop (nhds 0) := by
  refine WeightedLimitAux.cs_limit_tendsto (μ := volume.restrict Q0) (f := f) (h := h)
    (w := fun _ => (1 : ℝ)) (Filter.Eventually.of_forall fun _ => one_pos)
    (fun k => aesm_mul_one (hA k)) (aesm_div_one hB) (fun k => int_sq_mul_one (hAint k))
    (int_sq_div_one hBint) ?_
  refine hlim.congr' (Filter.Eventually.of_forall fun k => ?_)
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [mul_one])

/-- **The weighted `L²`-bound of a limit is inherited from a bounded, Cauchy family** — the
"limit passage" step of `hkMem_slots_of_approx`.

Let `T` be a differential operator with formal transpose `Tstar` (the hypothesis `hIBP`), `ρ > 0`
continuous on `Q0`, `ψ n → Φ` in `L²(Q0)` (with the finite-norm hypothesis `hL2mem`), and suppose
the transforms `T (ψ n)` are bounded in `L²(ρ² dzdθ)` by `B` and Cauchy there. Then `T Φ` lies in
`L²(ρ² dzdθ)` with the same bound.

Route. (1) `exists_subseq_ae_tendsto` gives a strictly monotone `φ` and `u` with
`T (ψ (φ k)) → u` a.e. and `∫ u²ρ² ≤ B`; (2) `tendsto_sq_sub_of_cauchy_of_ae` upgrades this to
`∫ (T (ψ (φ k)) - u)²ρ² → 0`; (3) `u = T Φ` a.e.: for every test function `φ'`,
`∫ u φ' = lim_k ∫ T (ψ (φ k)) φ' = lim_k ∫ ψ (φ k) (Tstar φ') = ∫ Φ (Tstar φ') = ∫ T Φ φ'`
(the first equality from the `L²(ρ²)` convergence and Cauchy–Schwarz against `φ'/ρ²`, the second
and fourth from `hIBP`, the third from `hL2t` and Cauchy–Schwarz against the bounded compactly
supported `Tstar φ'`), so `u - T Φ` integrates to `0` against every smooth compactly supported
function and Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` applies;
(4) the integrability and the bound transfer along this a.e. equality. -/
theorem weighted_le_of_limit {B : ℝ}
    {ρ : ℝ → ℝ → ℝ} (hρpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < ρ p.1 p.2)
    (hρcont : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0)
    {T Tstar : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)}
    (hIBP : ∀ {f φ : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen f → TestQ0 φ →
      TestQ0 (Tstar φ) ∧
      (∫ p in Work.FTS.EllipticEst.Q0, T f p.1 p.2 * φ p.1 p.2
        = ∫ p in Work.FTS.EllipticEst.Q0, f p.1 p.2 * Tstar φ p.1 p.2))
    {ψ : ℕ → ℝ → ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsmψ : ∀ n, Work.FTS.EllipticEst.SmoothOpen (ψ n))
    (hsmΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hTsm : ∀ n, Work.FTS.EllipticEst.SmoothOpen (T (ψ n)))
    (hTΦsm : Work.FTS.EllipticEst.SmoothOpen (T Φ))
    (hL2mem : ∀ n, IntegrableOn (fun p : ℝ × ℝ =>
      (ψ n p.1 p.2 - Φ p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0)
    (hL2t : Filter.Tendsto (fun n : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
      (ψ n p.1 p.2 - Φ p.1 p.2) ^ 2) Filter.Filter.atTop (nhds 0))
    (hint : ∀ n, IntegrableOn (fun p : ℝ × ℝ =>
      (T (ψ n) p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0)
    (hint2 : ∀ n m, IntegrableOn (fun p : ℝ × ℝ =>
      (T (ψ n) p.1 p.2 - T (ψ m) p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hb : ∀ n, (∫ p in Work.FTS.EllipticEst.Q0,
      (T (ψ n) p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2) ≤ B)
    (hcauchy : Filter.Tendsto (fun nm : ℕ × ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
      (T (ψ nm.1) p.1 p.2 - T (ψ nm.2) p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0)) :
    IntegrableOn (fun p : ℝ × ℝ => (T Φ p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 ∧
      (∫ p in Work.FTS.EllipticEst.Q0, (T Φ p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2) ≤ B := by
  classical
  have hQ0m : MeasurableSet Q0 := Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- #### 0. Positivity and measurability of the weight
  have hw_pos : ∀ᵐ p ∂(volume.restrict Q0), 0 < ρ p.1 p.2 := by
    rw [MeasureTheory.ae_restrict_iff' hQ0m]
    exact Filter.Eventually.of_forall fun p hp => hρpos p hp
  have hw_cont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Q0 := hρcont
  have hw_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2) (volume.restrict Q0) :=
    hρcont.aestronglyMeasurable hQ0m
  have hg_pos : ∀ᵐ p ∂(volume.restrict Q0), 0 < (ρ p.1 p.2) ^ 2 :=
    hw_pos.mono fun p h => pow_pos h 2
  have hg_nonneg : ∀ᵐ p ∂(volume.restrict Q0), 0 ≤ (ρ p.1 p.2) ^ 2 :=
    hg_pos.mono fun p h => h.le
  have hg_meas : AEMeasurable (fun p : ℝ × ℝ => (ρ p.1 p.2) ^ 2) (volume.restrict Q0) := by
    have h : (fun p : ℝ × ℝ => (ρ p.1 p.2) ^ 2)
        = (fun p : ℝ × ℝ => ρ p.1 p.2) * (fun p : ℝ × ℝ => ρ p.1 p.2) := by
      funext p; simp only [Pi.mul_apply]; ring
    rw [h]
    exact (hw_aesm.mul hw_aesm).aemeasurable
  have hTseq : ∀ n, AEStronglyMeasurable (fun p : ℝ × ℝ => T (ψ n) p.1 p.2)
      (volume.restrict Q0) :=
    fun n => (hTsm n).continuousOn.aestronglyMeasurable hQ0m
  have hTΦcont : ContinuousOn (fun p : ℝ × ℝ => T Φ p.1 p.2) Q0 := hTΦsm.continuousOn
  have hΦaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2) (volume.restrict Q0) :=
    hsmΦ.continuousOn.aestronglyMeasurable hQ0m
  -- #### 1. Extraction of an almost-everywhere limit of the bounded Cauchy family
  obtain ⟨ns, u, hns, huae, huint, hub⟩ :=
    exists_subseq_ae_tendsto (μ := volume.restrict Q0)
      (v := fun n p => T (ψ n) p.1 p.2) (g := fun p => (ρ p.1 p.2) ^ 2) (B := B)
      hg_pos hg_meas hTseq (fun n => hint n) (fun n m => hint2 n m) (fun n => hb n) hcauchy
  have husm : AEStronglyMeasurable u (volume.restrict Q0) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => hTseq (ns k)) huae
  have huw2 : Integrable (fun p : ℝ × ℝ => (u p * ρ p.1 p.2) ^ 2) (volume.restrict Q0) :=
    huint.congr (Filter.Eventually.of_forall fun p => by ring)
  have hnsT : Tendsto ns atTop atTop := hns.tendsto_atTop
  -- #### 2. The extracted subsequence converges to `u` in `L²(ρ² dzdθ)`
  have hcauchy_ns : Tendsto (fun nm : ℕ × ℕ =>
      ∫ p, (T (ψ (ns nm.1)) p.1 p.2 - T (ψ (ns nm.2)) p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2
        ∂(volume.restrict Q0)) (atTop ×ˢ atTop) (nhds 0) := by
    have h := hcauchy.comp (hnsT.prodMap hnsT)
    refine h.congr' (Filter.Eventually.of_forall fun nm => ?_)
    simp only [Function.comp_apply, Prod.map_def]
  have hL2_sub : Tendsto (fun k => ∫ p,
      (T (ψ (ns k)) p.1 p.2 - u p) ^ 2 * (ρ p.1 p.2) ^ 2 ∂(volume.restrict Q0))
      atTop (nhds 0) :=
    tendsto_sq_sub_of_cauchy_of_ae (μ := volume.restrict Q0)
      (v := fun k p => T (ψ (ns k)) p.1 p.2) (u := u) (g := fun p => (ρ p.1 p.2) ^ 2)
      hg_nonneg (fun n m => hint2 (ns n) (ns m)) hcauchy_ns huae
  -- #### 3. `u` and `T Φ` have the same pairing with every test function
  have key : ∀ φ : ℝ → ℝ → ℝ, TestQ0 φ →
      ∫ p, u p * φ p.1 p.2 ∂(volume.restrict Q0)
        = ∫ p, T Φ p.1 p.2 * φ p.1 p.2 ∂(volume.restrict Q0) := by
    intro φ hφ
    have hTstar : TestQ0 (Tstar φ) := (hIBP (hsmψ 0) hφ).1
    -- unweighted facts about `Tstar φ` (weight `≡ 1`)
    have hstar := WeightedLimitAux.test_weight_facts (ρ := fun _ _ => (1 : ℝ))
      (fun p _ => one_pos) continuousOn_const hTstar
    obtain ⟨_, _, hstar_sq, hstar_aesm, hstar_bd, hstar_supp⟩ := hstar
    obtain ⟨M, hMbd⟩ := hstar_bd
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMbd (0, 0))
    -- weighted facts about `φ`
    obtain ⟨hφw_int, hφw_sm, hφ2_int, hφ_sm, hφ_bd, hφ_suppfin⟩ :=
      WeightedLimitAux.test_weight_facts (ρ := ρ) hρpos hρcont hφ
    -- (a) the `ψ`-side limit passage `∫ (ψ_k - Φ)(T*φ) → 0`
    have hψlim0 : Tendsto (fun k => ∫ p,
        (ψ (ns k) p.1 p.2 - Φ p.1 p.2) * Tstar φ p.1 p.2 ∂(volume.restrict Q0))
        atTop (nhds 0) := by
      refine cs_limit_unweighted (f := fun k (p : ℝ × ℝ) => ψ (ns k) p.1 p.2 - Φ p.1 p.2)
        (h := fun p : ℝ × ℝ => Tstar φ p.1 p.2) ?_ ?_ ?_ ?_ ?_
      · intro k
        exact ((hsmψ (ns k)).continuousOn.sub hsmΦ.continuousOn).aestronglyMeasurable hQ0m
      · exact hstar_aesm
      · intro k; exact hL2mem (ns k)
      · exact hstar_sq
      · have h := hL2t.comp hnsT
        refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
        simp only [Function.comp_def]
    -- (b) the products `ψ_k · T*φ` and `Φ · T*φ` are integrable
    have hΦTstar_int : Integrable (fun p : ℝ × ℝ => Φ p.1 p.2 * Tstar φ p.1 p.2)
        (volume.restrict Q0) :=
      WeightedLimitAux.test_mul_continuousOn hTstar hsmΦ.continuousOn
    have hψTstar_int : ∀ k, Integrable (fun p : ℝ × ℝ => ψ (ns k) p.1 p.2 * Tstar φ p.1 p.2)
        (volume.restrict Q0) := by
      intro k
      have hs : MeasurableSet (tsupport (fun p : ℝ × ℝ => Tstar φ p.1 p.2)) :=
        hTstar.cpt.isCompact.isClosed.measurableSet
      exact WeightedLimitAux.integrable_mul_of_sq_sub_bounded
        (F := fun p : ℝ × ℝ => ψ (ns k) p.1 p.2) (G := fun p : ℝ × ℝ => Φ p.1 p.2)
        (h := fun p : ℝ × ℝ => Tstar φ p.1 p.2)
        (s := tsupport (fun p : ℝ × ℝ => Tstar φ p.1 p.2)) (M := M)
        hs hstar_supp (fun x hx => subset_closure (Function.mem_support.mpr hx))
        hM0 hMbd (hL2mem (ns k)) hΦTstar_int
        (((hsmψ (ns k)).continuousOn.aemeasurable hQ0m)) hstar_aesm.aemeasurable
    -- (c) `∫ ψ_k (T*φ) → ∫ Φ (T*φ)`
    have hψlim : Tendsto (fun k => ∫ p, ψ (ns k) p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))
        atTop (nhds (∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))) := by
      have hsplitψ : ∀ k, ∫ p, (ψ (ns k) p.1 p.2 - Φ p.1 p.2) * Tstar φ p.1 p.2
            ∂(volume.restrict Q0)
          = (∫ p, ψ (ns k) p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))
            - (∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0)) := by
        intro k
        rw [← integral_sub (hψTstar_int k) hΦTstar_int]
        exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
      have h1 : Tendsto (fun k =>
          (∫ p, ψ (ns k) p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))
            - (∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0)))
          atTop (nhds 0) :=
        hψlim0.congr' (Filter.Eventually.of_forall fun k => hsplitψ k)
      have h2 : Tendsto (fun k =>
          ((∫ p, ψ (ns k) p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))
            - (∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0)))
          + (∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0)))
          atTop (nhds (0 + ∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))) :=
        h1.add tendsto_const_nhds
      have h3 : Tendsto (fun k => ∫ p, ψ (ns k) p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))
          atTop (nhds (0 + ∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))) := by
        refine h2.congr' (Filter.Eventually.of_forall fun k => ?_)
        ring
      simpa only [zero_add] using h3
    -- (d) integrability on the `u`-side
    have hv2 : ∀ k, Integrable (fun p : ℝ × ℝ => (T (ψ (ns k)) p.1 p.2 * ρ p.1 p.2) ^ 2)
        (volume.restrict Q0) :=
      fun k => (hint (ns k)).congr (Filter.Eventually.of_forall fun p => by ring)
    have huφ_int : Integrable (fun p : ℝ × ℝ => u p * φ p.1 p.2) (volume.restrict Q0) :=
      WeightedLimitAux.integrable_mul_of_sq (f := u) (h := fun p : ℝ × ℝ => φ p.1 p.2)
        (w := fun p : ℝ × ℝ => ρ p.1 p.2) hw_pos husm hφ_sm huw2 hφw_int
    have hvφ_int : ∀ k, Integrable (fun p : ℝ × ℝ => T (ψ (ns k)) p.1 p.2 * φ p.1 p.2)
        (volume.restrict Q0) := fun k =>
      WeightedLimitAux.integrable_mul_of_sq (f := fun p : ℝ × ℝ => T (ψ (ns k)) p.1 p.2)
        (h := fun p : ℝ × ℝ => φ p.1 p.2) (w := fun p : ℝ × ℝ => ρ p.1 p.2) hw_pos
        (hTseq (ns k)) hφ_sm (hv2 k) hφw_int
    -- (e) the `u`-side limit passage
    have hu_lim : Tendsto (fun k => ∫ p,
        (u p - T (ψ (ns k)) p.1 p.2) * φ p.1 p.2 ∂(volume.restrict Q0)) atTop (nhds 0) := by
      refine WeightedLimitAux.cs_limit_tendsto (μ := volume.restrict Q0)
        (f := fun k (p : ℝ × ℝ) => u p - T (ψ (ns k)) p.1 p.2)
        (h := fun p : ℝ × ℝ => φ p.1 p.2) (w := fun p : ℝ × ℝ => ρ p.1 p.2)
        hw_pos ?_ hφw_sm ?_ hφw_int ?_
      · intro k; exact (husm.sub (hTseq (ns k))).mul hw_aesm
      · intro k
        exact WeightedLimitAux.integrable_sq_mul_sub
          (f₁ := u) (f₂ := fun p : ℝ × ℝ => T (ψ (ns k)) p.1 p.2)
          (w := fun p : ℝ × ℝ => ρ p.1 p.2)
          huw2 (hv2 k) ((husm.sub (hTseq (ns k))).mul hw_aesm)
      · refine hL2_sub.congr' (Filter.Eventually.of_forall fun k => ?_)
        exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    have hsplit_u : ∀ k, ∫ p, (u p - T (ψ (ns k)) p.1 p.2) * φ p.1 p.2 ∂(volume.restrict Q0)
        = (∫ p, u p * φ p.1 p.2 ∂(volume.restrict Q0))
          - (∫ p, T (ψ (ns k)) p.1 p.2 * φ p.1 p.2 ∂(volume.restrict Q0)) := by
      intro k
      rw [← integral_sub (huφ_int) (hvφ_int k)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    have hA : Tendsto (fun k => (∫ p, u p * φ p.1 p.2 ∂(volume.restrict Q0))
        - (∫ p, T (ψ (ns k)) p.1 p.2 * φ p.1 p.2 ∂(volume.restrict Q0)))
        atTop (nhds 0) :=
      hu_lim.congr' (Filter.Eventually.of_forall fun k => hsplit_u k)
    have hB : Tendsto (fun k => ∫ p, T (ψ (ns k)) p.1 p.2 * φ p.1 p.2 ∂(volume.restrict Q0))
        atTop (nhds (∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))) := by
      refine hψlim.congr' (Filter.Eventually.of_forall fun k => ?_)
      exact ((hIBP (hsmψ (ns k)) hφ).2).symm
    have hC := hA.add hB
    have hD : Tendsto (fun _ : ℕ => ∫ p, u p * φ p.1 p.2 ∂(volume.restrict Q0)) atTop
        (nhds (0 + ∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0))) :=
      hC.congr' (Filter.Eventually.of_forall fun k => by ring)
    have hE : ∫ p, u p * φ p.1 p.2 ∂(volume.restrict Q0)
        = 0 + ∫ p, Φ p.1 p.2 * Tstar φ p.1 p.2 ∂(volume.restrict Q0) :=
      tendsto_nhds_unique tendsto_const_nhds hD
    rw [hE, zero_add]
    exact ((hIBP hsmΦ hφ).2).symm
  -- #### 4. `u = T Φ` almost everywhere on `Q0`
  have hae_zero : ∀ᵐ p ∂(volume.restrict Q0), p ∈ Q0 → u p - T Φ p.1 p.2 = 0 := by
    refine IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (f := fun p : ℝ × ℝ => u p - T Φ p.1 p.2) Work.FTS.EllipticEst.isOpen_Q0 ?_ ?_
    · exact WeightedLimitAux.locallyIntegrableOn_sub hρpos hρcont husm huint hTΦcont
    · intro g hg hgcpt hgsupp
      have hφg : TestQ0 fun z θ => g (z, θ) := ⟨hg, hgcpt, hgsupp⟩
      obtain ⟨hgw_int, hgw_sm, hg2_int, hg_sm, hg_bd, hg_suppfin⟩ :=
        WeightedLimitAux.test_weight_facts (ρ := ρ) hρpos hρcont hφg
      have hug : Integrable (fun p : ℝ × ℝ => u p * g p) (volume.restrict Q0) :=
        WeightedLimitAux.integrable_mul_of_sq (f := u) (h := g) (w := fun p : ℝ × ℝ => ρ p.1 p.2)
          hw_pos husm hg_sm huw2 hgw_int
      have hTg : Integrable (fun p : ℝ × ℝ => T Φ p.1 p.2 * g p) (volume.restrict Q0) :=
        WeightedLimitAux.test_mul_continuousOn hφg hTΦcont
      have hkey := key (fun z θ => g (z, θ)) hφg
      have hsplit : ∫ x, g x • (u x - T Φ x.1 x.2) ∂(volume.restrict Q0)
          = (∫ x, u x * g x ∂(volume.restrict Q0))
            - (∫ x, T Φ x.1 x.2 * g x ∂(volume.restrict Q0)) := by
        rw [← integral_sub hug hTg]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [smul_eq_mul]
        ring
      rw [hsplit]
      have hsame : (∫ x, u x * g x ∂(volume.restrict Q0))
          = ∫ x, T Φ x.1 x.2 * g x ∂(volume.restrict Q0) := by
        simpa only [Prod.mk.eta] using hkey
      rw [hsame, sub_self]
  -- #### 5. Transfer of the integrability and of the bound
  have hae_prod : (fun p : ℝ × ℝ => u p ^ 2 * (ρ p.1 p.2) ^ 2) =ᵐ[volume.restrict Q0]
      (fun p : ℝ × ℝ => (T Φ p.1 p.2) ^ 2 * (ρ p.1 p.2) ^ 2) := by
    filter_upwards [hae_zero, MeasureTheory.ae_restrict_mem hQ0m] with p hp hpq
    have hup : u p = T Φ p.1 p.2 := sub_eq_zero.mp (hp hpq)
    rw [hup]
  refine ⟨huint.congr hae_prod, ?_⟩
  rw [← integral_congr_ae hae_prod]
  exact hub

end Work.FTS.PhiStar.Honesty.SlotsLimit
