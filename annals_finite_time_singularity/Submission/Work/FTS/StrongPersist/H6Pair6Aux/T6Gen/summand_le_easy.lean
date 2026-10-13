import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.N6TP.summandBound
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## The pointwise domination of a leaf-weighted slot by `HkIntegrand α 6`

The three leaf weights are the canonical weights `canonW q z θ = w(z)² sin(2θ)^{-q}` for
`q = η` (the pure `D_z`-slots), `q = 0` (the σ-free leaf) and `q = γ` (the mixed slots).
Each is pointwise dominated on the open quadrant by the corresponding slot weight of the
level-six integrand, which is the `canonW`-comparison of `SlotT2.Basic` read at level six. -/

/-- The pure-`D_z` slot: for `0 < q ≤ η` and `j ≤ 6` the weighted square
`canonW q · (D_z^j f)²` is dominated by the level-six integrand. -/
private lemma canonW_z_le_Hk6 (α : ℝ) (f : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ Work.Spaces.eta) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j : ℕ) (hj : j ≤ 6) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.DzIter j f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hw : Work.FTS.TransportS.SlotT2.canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← Work.FTS.TransportS.SlotT2.canonW_eta_eq z θ hθ]
    exact Work.FTS.TransportS.SlotT2.canonW_mono hq0 hq hθ
  calc Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.DzIter j f z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j f z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.DzIter j f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ j hj

/-- The mixed slot: for `0 < q ≤ γ` and `1 ≤ i`, `i + j ≤ 6` the weighted square
`canonW q · (D_z^jD_θ^i f)²` is dominated by the level-six integrand. -/
private lemma canonW_mixed_le_Hk6 (α : ℝ) (f : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hw : Work.FTS.TransportS.SlotT2.canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← Work.FTS.TransportS.SlotT2.canonW_gam_eq α z θ hθ]
    exact Work.FTS.TransportS.SlotT2.canonW_mono hq0 hqγ hθ
  calc Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i f z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i j hi hij

/-- **The leaf-weight domination at level six.**  For a leaf weight `ρ` of the slot `i`, all
slots `(i,j)` of order at most six and every point of the open quadrant,

`ρ z θ · (D_z^j D_θ^i f z θ)² ≤ HkIntegrand α 6 f z θ`.

The three cases are `ρ = leafEta` (compared with `canonW η` in the pure slots and with
`canonW γ` in the mixed ones, because `η ≤ γ`), `ρ = leafOne` (compared with `canonW η`
resp. `canonW γ`, both of which are at least `w²`) and `ρ = leafGam α` (which by `IsLeafW`
occurs only in a mixed slot, where it *is* `canonW γ`). -/
private lemma leaf_sq_le_Hk6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {i j : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α i ρ) (hij : i + j ≤ 6)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ρ z θ * (Work.Spaces.mixed j i f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hgam : (0 : ℝ) < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have heta : (0 : ℝ) < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  rcases hleaf with hρ | hρ | ⟨hi1, hρ⟩
  · -- the `η`-leaf
    subst hρ
    by_cases hi : 1 ≤ i
    · have hle : Work.FTS.TransportS.leafEta z θ
          ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
        rw [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.SlotT2.canonW]
        exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
      calc Work.FTS.TransportS.leafEta z θ * (Work.Spaces.mixed j i f z θ) ^ 2
          ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
              * (Work.Spaces.mixed j i f z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
            canonW_mixed_le_Hk6 α f hgam le_rfl hθI j i hi hij
    · have hi0 : i = 0 := by omega
      subst hi0
      rw [Work.Spaces.mixed_zero_right]
      exact canonW_z_le_Hk6 α f heta le_rfl hθI j (by omega)
  · -- the σ-free leaf `w²`
    subst hρ
    by_cases hi : 1 ≤ i
    · have hle : Work.FTS.TransportS.leafOne z θ
          ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
        rw [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW]
        have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          Work.FTS.TransportS.one_le_rpow_neg (q := Work.Spaces.gam α) hgam.le hθ
        simpa using mul_le_mul_of_nonneg_left h1 (sq_nonneg (Work.Spaces.w z))
      calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.mixed j i f z θ) ^ 2
          ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
              * (Work.Spaces.mixed j i f z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
            canonW_mixed_le_Hk6 α f hgam le_rfl hθI j i hi hij
    · have hi0 : i = 0 := by omega
      subst hi0
      have hle : Work.FTS.TransportS.leafOne z θ
          ≤ Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ := by
        rw [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW]
        have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          Work.FTS.TransportS.one_le_rpow_neg (q := Work.Spaces.eta) heta.le hθ
        simpa using mul_le_mul_of_nonneg_left h1 (sq_nonneg (Work.Spaces.w z))
      rw [Work.Spaces.mixed_zero_right]
      calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.DzIter j f z θ) ^ 2
          ≤ Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
              * (Work.Spaces.DzIter j f z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
            canonW_z_le_Hk6 α f heta le_rfl hθI j (by omega)
  · -- the `γ`-leaf, which occurs only in a mixed slot, where it is `canonW γ`
    subst hρ
    exact canonW_mixed_le_Hk6 α f hgam le_rfl hθI j i hi1 hij

/-! ## The main theorem -/

/-- **The easy summand bound of the level-six pairing.**  If `F` is a bounded multiplier
(`|F| ≤ K` on the open quadrant) and `ρ` is a leaf weight of the slot `(a,b)` which is also
admissible for the slot `(a₀,b₀)` (which is what the guard
`1 ≤ a₀ ∨ ρ = leafEta ∨ ρ = leafOne` says), then the summand
`ρ·F·(D_z^{b₀}D_θ^{a₀}f)·(D_z^bD_θ^af)` is product-integrable on `Iz ×ˢ Iθ` and its integral
is bounded by `K·HkSq α 6 f`.

The pointwise input is the AM–GM pair estimate
`|ρ F m₀ m| ≤ K·(ρ m₀² + ρ m²)/2 ≤ K·HkIntegrand α 6 f`, valid on the open quadrant (a conull
set), each of the two leaf-weighted slots being dominated by the level-six integrand
(`leaf_sq_le_Hk6`); the passage to the product integral is `N6TP.summand_ae_package`. -/
theorem summand_le_easy : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (F f : ℝ → ℝ → ℝ) (a₀ b₀ a b : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen F → 0 ≤ K →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |F z θ| ≤ K) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      a₀ + b₀ ≤ 6 → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (1 ≤ a₀ ∨ ρ = Work.FTS.TransportS.leafEta ∨ ρ = Work.FTS.TransportS.leafOne) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * F p.1 p.2
          * Work.Spaces.mixed b₀ a₀ f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
        |∫ p, ρ p.1 p.2 * F p.1 p.2
              * Work.Spaces.mixed b₀ a₀ f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
          ≤ C * K * Work.Spaces.HkSq α 6 f := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα F f a₀ b₀ a b ρ K hF hK hFbd hf hmem ha₀b₀ hab hleaf hguard
  have hαpos : 0 < α := hα.1
  -- the leaf weight `ρ` of the slot `(a,b)` is also admissible for the slot `(a₀,b₀)`
  have hleaf₀ : Work.FTS.TransportS.IsLeafW α a₀ ρ := by
    rcases hguard with h | h | h
    · rcases hleaf with h1 | h1 | ⟨h2, h1⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨h, h1⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ :=
    (Work.FTS.TransportS.IsLeafW_le α hαpos hleaf).1
  -- continuity of the leaf weight on the open quadrant
  have hρcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rcases hleaf with rfl | rfl | ⟨_, rfl⟩
    · exact Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta
    · refine (Work.FTS.TransportS.SlotT2.continuousOn_canonW 0).congr ?_
      intro p _
      simp [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW]
    · exact Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2 * F p.1 p.2
      * Work.Spaces.mixed b₀ a₀ f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (((hρcont.mul hF.continuousOn).mul (hf.mixed b₀ a₀).continuousOn).mul
      (hf.mixed b a).continuousOn)
  -- the pointwise bound on the open quadrant
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ‖(fun p : ℝ × ℝ => ρ p.1 p.2 * F p.1 p.2 * Work.Spaces.mixed b₀ a₀ f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) (z, θ)‖
        ≤ K * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hnn : 0 ≤ ρ z θ := hρnn z θ hz hθ0 hθ1
    have hA : ρ z θ * (Work.Spaces.mixed b₀ a₀ f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := leaf_sq_le_Hk6 hαpos hleaf₀ ha₀b₀ hθ
    have hB : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := leaf_sq_le_Hk6 hαpos hleaf hab hθ
    have hFabs : |F z θ| ≤ K := hFbd z θ hz hθ0 hθ1
    have h2ab : 2 * |Work.Spaces.mixed b₀ a₀ f z θ| * |Work.Spaces.mixed b a f z θ|
        ≤ (Work.Spaces.mixed b₀ a₀ f z θ) ^ 2 + (Work.Spaces.mixed b a f z θ) ^ 2 := by
      have h := sq_nonneg (|Work.Spaces.mixed b₀ a₀ f z θ| - |Work.Spaces.mixed b a f z θ|)
      rw [sub_sq, sq_abs, sq_abs] at h
      linarith
    have hstep1 : ρ z θ * |F z θ| * |Work.Spaces.mixed b₀ a₀ f z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ ρ z θ * K * |Work.Spaces.mixed b₀ a₀ f z θ| * |Work.Spaces.mixed b a f z θ| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFabs hnn) (abs_nonneg _))
        (abs_nonneg _)
    have hstep2 : ρ z θ * K * |Work.Spaces.mixed b₀ a₀ f z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ K * (ρ z θ * ((Work.Spaces.mixed b₀ a₀ f z θ) ^ 2
            + (Work.Spaces.mixed b a f z θ) ^ 2)) / 2 := by
      have hρK : 0 ≤ ρ z θ * K := mul_nonneg hnn hK
      have h := mul_le_mul_of_nonneg_left h2ab hρK
      linarith
    have hstep3 : K * (ρ z θ * ((Work.Spaces.mixed b₀ a₀ f z θ) ^ 2
          + (Work.Spaces.mixed b a f z θ) ^ 2)) / 2 ≤ K * Work.Spaces.HkIntegrand α 6 f z θ := by
      have hsum : ρ z θ * ((Work.Spaces.mixed b₀ a₀ f z θ) ^ 2
          + (Work.Spaces.mixed b a f z θ) ^ 2) ≤ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
        linarith
      have h := mul_le_mul_of_nonneg_left hsum hK
      linarith
    calc ‖(fun p : ℝ × ℝ => ρ p.1 p.2 * F p.1 p.2 * Work.Spaces.mixed b₀ a₀ f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2) (z, θ)‖
        = ρ z θ * |F z θ| * |Work.Spaces.mixed b₀ a₀ f z θ|
            * |Work.Spaces.mixed b a f z θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hnn]
      _ ≤ ρ z θ * K * |Work.Spaces.mixed b₀ a₀ f z θ| * |Work.Spaces.mixed b a f z θ| :=
          hstep1
      _ ≤ K * (ρ z θ * ((Work.Spaces.mixed b₀ a₀ f z θ) ^ 2
            + (Work.Spaces.mixed b a f z θ) ^ 2)) / 2 := hstep2
      _ ≤ K * Work.Spaces.HkIntegrand α 6 f z θ := hstep3
  obtain ⟨hint, hbd⟩ := Work.FTS.StrongPersist.N6TP.summand_ae_package (α := α) (g := f)
    (F := fun p : ℝ × ℝ => ρ p.1 p.2 * F p.1 p.2 * Work.Spaces.mixed b₀ a₀ f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2)
    (M := K) hf hmem hcont hpt
  exact ⟨hint, hbd.trans (le_of_eq (by ring))⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
