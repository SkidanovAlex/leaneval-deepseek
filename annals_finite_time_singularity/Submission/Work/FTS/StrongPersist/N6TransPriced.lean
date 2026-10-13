import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.StrongPersist.N6Trans.slotT1Six
import Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6TP.summandBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.N6TransPriced`

The level-six transport clauses `T1/T2/T3` for the concrete coercive pairing `IP6 1 … 1`.

`IP6 1 … 1 = IPn α 5` (the five-fold iterate above `H1IP`), and the proved unfolding bound
`TransportS.ip4_unfold_bound` dominates `IPn α 5 u v` by `3^5 · 10^22 · SlotSum α 6 u v`, the
sum of the absolute values of the leaf slot pairings over the `28` slots `a + b ≤ 6` with the
three leaf weights `leafEta`, `leafOne`, `leafGam α` (`a ≥ 1`).  Hence each clause follows from
the corresponding *per-slot* estimate at level six:

* `slotT1Six` (`D_θ`-transport with an `ℋ⁶`-coefficient) — proved elsewhere in the tree;
* `slotT2Six` (`D_z`-transport with a flat angular coefficient of order 1) — proved elsewhere;
* `slotT3Coef5` (below): the paper's `Transport3` at level six, in the priced form
  `WlInf α 6 f + CoefTh 5 f` with the matching hypothesis `CoefThMem 5 f`.

The per-slot `D_z`-transport bound is obtained from the exact Leibniz expansion
`SixRoute.sixExpansion` and the per-summand estimate `N6TP.summandBound`; the one non-pointwise
branch is the leaf `(a₁,b₁) = (0,0)`, which is the radial integration by parts of
`SixRoute.fluxFamSix` / `fluxFamSixTop`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6TPPriced

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary closure of `SmoothOpen` -/

/-- `SmoothOpen` is closed under products (interior `C^∞` on the open quadrant). -/
theorem SmoothOpen.mul {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  convert hF.mul hG using 1
  ext p
  rfl

/-! ## The `IP6` unfolding -/

/-- `IPn α 5` is the concrete `IP6 1 1 1 1 1 1 1 1 1 1`. -/
theorem IP6_one_eq_IPn_five (α : ℝ) (u v : Fn) :
    Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u v = Work.FTS.TransportS.IPn α 5 u v := by
  have hIP6 : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
      = Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1
          (Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α)) := rfl
  have h5 : Work.FTS.TransportS.IPn α 5
      = Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1
          (Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α)) := rfl
  rw [hIP6, h5]

/-- The level-six slot sum is bounded by `84 * B` when every leaf slot is bounded by `B`:
there are `28` slots `(a,b)` with `a + b ≤ 6` and three leaf weights each. -/
theorem SlotSum_six_le (α : ℝ) (u v : Fn) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b u v| ≤ B) :
    Work.FTS.TransportS.SlotSum α 6 u v ≤ 84 * B := by
  have hterm : ∀ a ∈ Finset.range 7, ∀ b ∈ Finset.range (7 - a),
      Work.FTS.TransportS.SlotTerm α a b u v ≤ 3 * B := by
    intro a ha b hb
    have hab : a + b ≤ 6 := by
      have h1 : a ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have h2 : b < 7 - a := Finset.mem_range.mp hb
      omega
    have hE := hB a b Work.FTS.TransportS.leafEta hab (Or.inl rfl)
    have hO := hB a b Work.FTS.TransportS.leafOne hab (Or.inr (Or.inl rfl))
    have hG : (if 1 ≤ a then
        |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u v| else 0) ≤ B := by
      by_cases h : 1 ≤ a
      · rw [ite_eq_left h]
        exact hB a b (Work.FTS.TransportS.leafGam α) hab (Or.inr (Or.inr ⟨h, rfl⟩))
      · rw [ite_eq_right h]; exact hB0
    calc Work.FTS.TransportS.SlotTerm α a b u v
        = |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u v|
          + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u v|
          + (if 1 ≤ a then
              |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u v| else 0) := rfl
      _ ≤ B + B + B := by linarith
      _ = 3 * B := by ring
  calc Work.FTS.TransportS.SlotSum α 6 u v
      = ∑ a ∈ Finset.range 7, ∑ b ∈ Finset.range (7 - a),
          Work.FTS.TransportS.SlotTerm α a b u v :=
        Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm α 6 u v
    _ ≤ ∑ a ∈ Finset.range 7, ∑ b ∈ Finset.range (7 - a), (3 * B) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = ∑ a ∈ Finset.range 7, ((7 - a : ℕ) : ℝ) * (3 * B) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (∑ a ∈ Finset.range 7, ((7 - a : ℕ) : ℝ)) * (3 * B) := by
        rw [Finset.sum_mul]
    _ = 84 * B := by
        have h : (∑ a ∈ Finset.range 7, (7 - a)) = 28 := by decide
        have h' : (∑ a ∈ Finset.range 7, ((7 - a : ℕ) : ℝ)) = 28 := by
          exact_mod_cast h
        rw [h']; ring

/-! ## The level-six `D_z`-transport slot bound with a flat coefficient of order five -/

/-- **The per-slot `D_z`-transport bound at level six**, in the priced form the clause
`T3Clause6` asks for. -/
theorem slotT3Coef5 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f g : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.VocabO.CoefThMem 5 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
    a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  obtain ⟨Cs, hCs0, hS⟩ := Work.FTS.StrongPersist.N6TP.summandBound
  refine ⟨128 * Cs, by positivity, ?_⟩
  intro α hα f g a b ρ hf hfw hfc hg hgm hgm7 hdec hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hHs0 : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  set M : ℝ := Cs * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
      * Work.Spaces.HkSq α 6 g with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (mul_nonneg hCs0.le (add_nonneg (Work.Spaces.WlInf_nonneg α 6 f hfw)
      (Work.FTS.TransportS.coefTh_nonneg 5 f))) hHs0
  have hint : ∀ a₁ ≤ a, ∀ b₁ ≤ b, MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b₁ a₁ f p.1 p.2
      * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    fun a₁ ha₁ b₁ hb₁ => (hS α hα f g a b a₁ b₁ ρ hf hfw hfc hg hgm hgm7 hdec hab hleaf ha₁ hb₁).1
  have hbd : ∀ a₁ ≤ a, ∀ b₁ ≤ b, |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
      * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))| ≤ M := by
    intro a₁ ha₁ b₁ hb₁
    have h := (hS α hα f g a b a₁ b₁ ρ hf hfw hfc hg hgm hgm7 hdec hab hleaf ha₁ hb₁).2
    rw [hM]
    exact h
  have hsum_int : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
              * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.integrable_finsetSum (Finset.range (a + 1)) fun a₁ ha₁ => ?_
    refine MeasureTheory.integrable_finsetSum (Finset.range (b + 1)) fun b₁ hb₁ => ?_
    exact (hint a₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)) b₁
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))).const_mul
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
  have hae : (fun p : ℝ × ℝ =>
      ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
              * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2))
      =ᵐ[(MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
      (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
              * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2))
        = ρ p.1 p.2
          * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2) ?_
    intro z θ hz hθ0 hθ1
    rw [Work.FTS.TransportS.mixed_mul_Dz_open b a f g hf hg z θ hz hθ0 hθ1]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
    ring
  have hXY : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.Integrable.congr hsum_int hae
  rw [Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion (α := α) a b ρ hf hg hXY hint]
  have hbinom : (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) = (2 : ℝ) ^ a * (2 : ℝ) ^ b := by
    rw [← Finset.sum_mul_sum]
    congr 1
    · exact_mod_cast Nat.sum_range_choose a
    · exact_mod_cast Nat.sum_range_choose b
  have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
    rw [← pow_add]
    calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hab
      _ = 64 := by norm_num
  have hX1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hα0.le]
    rw [one_le_inv₀ (Real.rpow_pos_of_pos hα0 (1 / 2 : ℝ))]
    exact Real.rpow_le_one hα0.le hα1 (by norm_num)
  have hsq : (Work.Spaces.HkNorm α 6 g) ^ 2 = Work.Spaces.HkSq α 6 g :=
    Real.sq_sqrt hHs0
  rw [hsq]
  calc |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
                * Work.Spaces.mixed b a g p.1 p.2
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)))|
      ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
                * Work.Spaces.mixed b a g p.1 p.2
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)))| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun a₁ _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * M := by
        refine Finset.sum_le_sum fun a₁ ha₁ => Finset.sum_le_sum fun b₁ hb₁ => ?_
        have ha₁' : a₁ ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)
        have hb₁' : b₁ ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
        rw [abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose a₁ : ℝ)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose b₁ : ℝ))]
        exact mul_le_mul_of_nonneg_left (hbd a₁ ha₁' b₁ hb₁') (by positivity)
      _ = (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) * M := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.sum_mul]
      _ = (2 : ℝ) ^ a * (2 : ℝ) ^ b * M := by rw [hbinom]
      _ ≤ 64 * M := mul_le_mul_of_nonneg_right hpow hM0
      _ ≤ 128 * Cs * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
            * Work.Spaces.HkSq α 6 g := by
        have hW0 : 0 ≤ Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f :=
          add_nonneg (Work.Spaces.WlInf_nonneg α 6 f hfw)
            (Work.FTS.TransportS.coefTh_nonneg 5 f)
        have hWK : 0 ≤ (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
            * Work.Spaces.HkSq α 6 g := mul_nonneg hW0 hHs0
        have hkey : 64 * (Cs * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
            * Work.Spaces.HkSq α 6 g)
            ≤ 128 * Cs * α ^ (-(1 / 2 : ℝ))
              * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
              * Work.Spaces.HkSq α 6 g := by
          nlinarith [hCs0, hX1, hWK, hHs0, hW0, mul_nonneg hCs0.le hWK]
        rw [hM]
        exact hkey

/-! ## The three clauses from the per-slot bounds -/

/-- **The `t1` clause at level six from the per-slot `D_θ` bounds.** -/
theorem T1Clause6_of_slot {A C1 : ℝ} (hC1 : 0 < C1)
    (hsl : ∀ α ∈ Set.Ioc 0 A, ∀ (f g : Fn) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
        ≤ C1 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
            * (Work.Spaces.HkNorm α 6 g) ^ 2) :
    Work.FTS.StrongPersist.T1Clause6 (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) A
      (3 ^ 5 * 10 ^ 22 * 84 * C1) := by
  intro α hα f g hf hg
  obtain ⟨hF, hmF⟩ := hf
  obtain ⟨hG, hmG⟩ := hg
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dth g z θ) :=
    SmoothOpen.mul hF hG.Dth
  have hIP := IP6_one_eq_IPn_five α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g
  have hb := Work.FTS.TransportS.ip4_unfold_bound 5 α
    (fun z θ => f z θ * Work.Spaces.Dth g z θ) g hsm hG
  rw [← hIP] at hb
  have hX0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hY0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
  have hr0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
  set P : ℝ := C1 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
    * (Work.Spaces.HkNorm α 6 g) ^ 2 with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC1.le hr0) hX0) (sq_nonneg _)
  have hsl' := SlotSum_six_le α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g P hP0
    (fun a b ρ hab hρ => hsl α hα f g a b ρ hF hmF hG hmG hab hρ)
  have h220 : (0 : ℝ) ≤ 3 ^ 5 * 10 ^ 22 := by positivity
  refine le_trans hb (le_trans (mul_le_mul_of_nonneg_left hsl' h220) (le_of_eq ?_))
  simp only [hP]
  ring

/-- **The `t2` clause at level six from the per-slot `D_z` bounds.** -/
theorem T2Clause6_of_slot {A C2 : ℝ} (hC2 : 0 < C2)
    (hsl : ∀ α ∈ Set.Ioc 0 A, ∀ (f g : Fn) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.VocabO.CoefThMem 1 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C2 * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2) :
    Work.FTS.StrongPersist.T2Clause6 (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) A
      (3 ^ 5 * 10 ^ 22 * 84 * C2) := by
  intro α hα f g hF hmF hcf hg hm7 hdec
  obtain ⟨hG, hmG⟩ := hg
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
    SmoothOpen.mul hF hG.Dz
  have hIP := IP6_one_eq_IPn_five α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
  have hb := Work.FTS.TransportS.ip4_unfold_bound 5 α
    (fun z θ => f z θ * Work.Spaces.Dz g z θ) g hsm hG
  rw [← hIP] at hb
  have hX0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hK0 : (0 : ℝ) ≤ Work.FTS.VocabO.CoefTh 1 f := Work.FTS.TransportS.coefTh_nonneg 1 f
  have hr0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
  set P : ℝ := C2 * α ^ (-(1 / 2 : ℝ))
    * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
    * (Work.Spaces.HkNorm α 6 g) ^ 2 with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC2.le hr0) (add_nonneg hX0 hK0)) (sq_nonneg _)
  have hsl' := SlotSum_six_le α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g P hP0
    (fun a b ρ hab hρ => hsl α hα f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ)
  have h220 : (0 : ℝ) ≤ 3 ^ 5 * 10 ^ 22 := by positivity
  refine le_trans hb (le_trans (mul_le_mul_of_nonneg_left hsl' h220) (le_of_eq ?_))
  simp only [hP]
  ring

/-- **The `t3` clause at level six from the per-slot `D_z` bounds** (`CoefThMem 5` priced). -/
theorem T3Clause6_of_slot {A C3 : ℝ} (hC3 : 0 < C3)
    (hsl : ∀ α ∈ Set.Ioc 0 A, ∀ (f g : Fn) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.VocabO.CoefThMem 5 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C3 * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2) :
    Work.FTS.StrongPersist.T3Clause6 (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) A
      (3 ^ 5 * 10 ^ 22 * 84 * C3) := by
  intro α hα f g hF hmF hcf hg hm7 hdec
  obtain ⟨hG, hmG⟩ := hg
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
    SmoothOpen.mul hF hG.Dz
  have hIP := IP6_one_eq_IPn_five α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
  have hb := Work.FTS.TransportS.ip4_unfold_bound 5 α
    (fun z θ => f z θ * Work.Spaces.Dz g z θ) g hsm hG
  rw [← hIP] at hb
  have hr0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
  set P : ℝ := C3 * α ^ (-(1 / 2 : ℝ))
    * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
    * (Work.Spaces.HkNorm α 6 g) ^ 2 with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    have h1 : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hmF
    have h2 : 0 ≤ Work.FTS.VocabO.CoefTh 5 f := Work.FTS.TransportS.coefTh_nonneg 5 f
    exact mul_nonneg (mul_nonneg (mul_nonneg hC3.le hr0) (add_nonneg h1 h2)) (sq_nonneg _)
  have hsl' := SlotSum_six_le α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g P hP0
    (fun a b ρ hab hρ => hsl α hα f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ)
  have h220 : (0 : ℝ) ≤ 3 ^ 5 * 10 ^ 22 := by positivity
  refine le_trans hb (le_trans (mul_le_mul_of_nonneg_left hsl' h220) (le_of_eq ?_))
  simp only [hP]
  ring

end Work.FTS.StrongPersist.N6TPPriced

namespace Work.FTS.StrongPersist

/-! ## The final assembly -/

/-- **The level-six transport clauses for the concrete `IP6` with all step coefficients `1`.** -/
theorem N6TransPriced : ∃ α₂ Ct : ℝ, 0 < Ct ∧ 0 < α₂ ∧
    Work.FTS.StrongPersist.N6Trans (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ct := by
  obtain ⟨C1, a1, hC1, ha1, h1⟩ := Work.FTS.StrongPersist.N6Trans.slotT1Six
  obtain ⟨C2, a2, hC2, ha2, h2⟩ := Work.FTS.StrongPersist.N6Trans.slotT2Six
  obtain ⟨C3, hC3, h3⟩ := N6TPPriced.slotT3Coef5
  have hCtot : 0 < 3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3) := by positivity
  set A : ℝ := min 1 (min a1 (min a2 1)) with hA
  have hA0 : 0 < A := by
    rw [hA]; exact lt_min one_pos (lt_min ha1 (lt_min ha2 one_pos))
  have hA1 : A ≤ 1 := by rw [hA]; exact min_le_left _ _
  have hAa1 : A ≤ a1 := by
    rw [hA]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hAa2 : A ≤ a2 := by
    rw [hA]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have t1 : Work.FTS.StrongPersist.T1Clause6 (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) A
      (3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3)) :=
    N6TPPriced.T1Clause6_of_slot (A := A) (C1 := C1 + C2 + C3) (by positivity)
      (fun α hα f g a b ρ hF hmF hG hmG hab hρ => by
        have hr := h1 α ⟨hα.1, le_trans hα.2 hAa1⟩ f g a b ρ hF hmF hG hmG hab hρ
        have hX0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
        have hX1 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
        have hX2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
        have hX : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
            * (Work.Spaces.HkNorm α 6 g) ^ 2 :=
          mul_nonneg (mul_nonneg hX0 hX1) (sq_nonneg _)
        calc |Work.FTS.TransportS.slotPairing ρ a b
              (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
            ≤ C1 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := hr
          _ = C1 * (α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 6 g) ^ 2) := by ring
          _ ≤ (C1 + C2 + C3) * (α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 6 g) ^ 2) :=
              mul_le_mul_of_nonneg_right (by linarith) hX
          _ = (C1 + C2 + C3) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring)
  have t2 : Work.FTS.StrongPersist.T2Clause6 (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) A
      (3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3)) :=
    N6TPPriced.T2Clause6_of_slot (A := A) (C2 := C1 + C2 + C3) (by positivity)
      (fun α hα f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ => by
        have hr := h2 α ⟨hα.1, le_trans hα.2 hAa2⟩ f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ
        have hX0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
        have hX1 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f :=
          add_nonneg (Work.Spaces.HkNorm_nonneg α 6 f) (Work.FTS.TransportS.coefTh_nonneg 1 f)
        have hX2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
        have hX : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2 :=
          mul_nonneg (mul_nonneg hX0 hX1) (sq_nonneg _)
        calc |Work.FTS.TransportS.slotPairing ρ a b
              (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
            ≤ C2 * α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := hr
          _ = C2 * (α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2) := by ring
          _ ≤ (C1 + C2 + C3) * (α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2) :=
              mul_le_mul_of_nonneg_right (by linarith) hX
          _ = (C1 + C2 + C3) * α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring)
  have t3 : Work.FTS.StrongPersist.T3Clause6 (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) A
      (3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3)) :=
    N6TPPriced.T3Clause6_of_slot (A := A) (C3 := C1 + C2 + C3) (by positivity)
      (fun α hα f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ => by
        have hr := h3 α ⟨hα.1, le_trans hα.2 hA1⟩ f g a b ρ hF hmF hcf hG hmG hm7 hdec hab hρ
        have hX0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
        have hX1 : (0 : ℝ) ≤ Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f :=
          add_nonneg (Work.Spaces.WlInf_nonneg α 6 f hmF) (Work.FTS.TransportS.coefTh_nonneg 5 f)
        have hX2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
        have hX : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2 :=
          mul_nonneg (mul_nonneg hX0 hX1) (sq_nonneg _)
        calc |Work.FTS.TransportS.slotPairing ρ a b
              (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
            ≤ C3 * α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := hr
          _ = C3 * (α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2) := by ring
          _ ≤ (C1 + C2 + C3) * (α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2) :=
              mul_le_mul_of_nonneg_right (by linarith) hX
          _ = (C1 + C2 + C3) * α ^ (-(1 / 2 : ℝ))
                * (Work.Spaces.WlInf α 6 f + Work.FTS.VocabO.CoefTh 5 f)
                * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring)
  exact ⟨A, 3 ^ 5 * 10 ^ 22 * 84 * (C1 + C2 + C3), hCtot, hA0,
    ⟨⟨hCtot, hA0⟩, t1, t2, t3⟩⟩

end Work.FTS.StrongPersist
