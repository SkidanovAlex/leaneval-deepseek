import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.STEasyId
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.T3S
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
-- ===== merged: Submission.Work.FTS.TransportS.GoodOpenBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The two smoothness bridges -/

/-- `SmoothQuad` implies `SmoothOpen` (`Q0 ⊆ quadU`). -/
theorem smoothOpen_of_smoothQuad {F : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad F) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  h.mono fun p hp =>
    ⟨show (-1 : ℝ) < p.1 by linarith [show (0 : ℝ) < p.1 from hp.1], hp.2⟩

/-- `SmoothOpen` implies the finite-order form `∀ n, C^n` on the open quadrant, which is the
hypothesis shape of the open-set commutation lemmas. -/
theorem smoothOpen_forall_nat {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp h

/-- `D_z` preserves `SmoothOpen`. -/
theorem smoothOpen_Dz {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz F) :=
  Work.FTS.LocData.contDiffOn_Dz Work.FTS.EllipticEst.isOpen_Q0 h

/-! ## The multiplier bound in the open class -/

/-- **The `f`-side bound for mixed derivatives in the open class.**  Every mixed derivative
`D_z^bD_θ^a f` of total order at most `4` of a `SmoothOpen` function `f` of class
`𝒲^{4,∞}` is bounded at every interior point by `200 |f|_{𝒲^{4,∞}}`.

This is the `SmoothOpen` analogue of `Work.FTS.H2.T3Q.abs_mixed_le_WlInf_Q` (whose constant
is `30`); the constant is larger here because the open-quadrant estimates give
`100|f|_𝒲 · (α + sin 2θ)sin(2θ)^{α/5}` and only `(α + sin 2θ)sin(2θ)^{α/5} ≤ 2` is available
for `0 < α ≤ 1`. -/
theorem abs_mixed_le_WlInf_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.WlInfMem α 4 f)
    {a b : ℕ} (hab : a + b ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 200 * Work.Spaces.WlInf α 4 f := by
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.FTS.H2.WPQ.WlInf_nonneg' hmem
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp only [Work.Spaces.mixed_zero_right]
    calc |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f :=
          Work.FTS.OpenPkg.DzIter_le_WlInf_open hf hmem (by omega) hz hθ
      _ ≤ 200 * Work.Spaces.WlInf α 4 f := by linarith
  · have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hα5 : 0 ≤ α / 5 := by linarith
    have hΦ1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 hα5
    have hΦ2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
      have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
      nlinarith [hΦ1, Real.rpow_nonneg hs0 (α / 5), hs0, hα]
    calc |Work.Spaces.mixed b a f z θ|
        ≤ 100 * (Work.Spaces.WlInf α 4 f
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Work.FTS.OpenPkg.Mixed_le_WlInf_open hα hf hmem ha (by omega) hz hθ
      _ ≤ 100 * (Work.Spaces.WlInf α 4 f * 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦ2 hW) (by norm_num)
      _ = 200 * Work.Spaces.WlInf α 4 f := by ring

/-! ## The two Leibniz rules for the factor `D_z g` -/


/-- **`D_θ^n (D_z g) = D_z (D_θ^n g)`, hence `D_z^mD_θ^n (D_z g) = D_z^{m+1}D_θ^n g` on the
open quadrant**, for `g` of class `SmoothOpen`. -/
theorem mixed_Dz_eq_open {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (m n : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed m n (Work.Spaces.Dz g) z θ = Work.Spaces.mixed (m + 1) n g z θ := by
  intro z θ hz hθ0 hθ1
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hcomm : Set.EqOn
      (Function.uncurry (Work.Spaces.DthIter n (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter n g)))
      Work.FTS.EllipticEst.Q0 := by
    have h := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 (smoothOpen_forall_nat hg) 1 n
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.mixed] using h
  have hc := Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcomm m hy
  show Work.Spaces.DzIter m (Work.Spaces.DthIter n (Work.Spaces.Dz g)) z θ
      = Work.Spaces.DzIter (m + 1) (Work.Spaces.DthIter n g) z θ
  rw [show Work.Spaces.DzIter m (Work.Spaces.DthIter n (Work.Spaces.Dz g)) z θ
        = Work.Spaces.DzIter m (Work.Spaces.Dz (Work.Spaces.DthIter n g)) z θ from hc]
  exact congrFun (congrFun
    (Work.FTS.H2.Transport3Aux.Z3.DzIter_Dz m (Work.Spaces.DthIter n g)) z) θ

/-- **Leibniz expansion of `D_z^jD_θ^i (f · D_zg)` in the open class.** -/
theorem mixed_mul_Dz_open (j i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ
                  * Work.Spaces.mixed (j - b + 1) (i - a) g z θ) := by
  intro z θ hz hθ0 hθ1
  rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i f (Work.Spaces.Dz g) hf
    (smoothOpen_Dz hg) z θ hz hθ0 hθ1]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [mixed_Dz_eq_open hg (j - b) (i - a) z θ hz hθ0 hθ1]

end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.FTS.TransportS.Slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The elementary slot pairing -/

/-- The elementary slot pairing `∫_z ∫_θ ρ · D_z^bD_θ^a u · D_z^bD_θ^a v`.  Every leaf of the
unfolding of the coercive `IP4` is one of these (up to a scalar), and every slot of the flat
pairing `H4Pair` is `slotPairing (slotW α a) a b u v`. -/
def slotPairing (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (u v : Fn) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a v z θ


/-! ## The leaf weights of `IP4` -/

/-- The three leaf weights of `H1IP`, as functions of `(z,θ)`:
`w² sin(2θ)^{-η}` (the `10`- and `10^10`-terms of `H1IP`), `w²` (the `10^17`-term) and
`w² sin(2θ)^{-γ}` (the `10^21`-term).  These are exactly the weights occurring in the unfolding
of `IP4`, and they are all smooth in `z` with `z ∂_z(ρ)/ρ = (z-3)/(1+z)` bounded — this is what
the radial integration by parts of the five top slots needs, and what the refuted
"arbitrary weight `ρ ≤ slotW α a`" version of the per-slot bound was missing
(`NOTES_t2Slot_FALSE.md`). -/
def leafEta : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The σ-free leaf weight `w²`. -/
def leafOne : ℝ → ℝ → ℝ := fun z _ => (Work.Spaces.w z) ^ 2

/-- The `γ` leaf weight `w² sin(2θ)^{-γ}`. -/
def leafGam (α : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

theorem leafEta_nonneg {z θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) : 0 ≤ leafEta z θ :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hθ _)

theorem leafOne_nonneg (z θ : ℝ) : 0 ≤ leafOne z θ := sq_nonneg _

theorem leafGam_nonneg (α : ℝ) {z θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) :
    0 ≤ leafGam α z θ := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hθ _)

/-- For `0 < sin(2θ)` and `q ≥ 0` the weight `sin(2θ)^{-q}` is at least `1`. -/
theorem one_le_rpow_neg {q θ : ℝ} (hq : 0 ≤ q) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-q) := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_one hσ.le hσ1 hq
  have hpos : 0 < Real.sin (2 * θ) ^ q := Real.rpow_pos_of_pos hσ q
  rw [Real.rpow_neg hσ.le]
  exact (one_le_inv₀ hpos).mpr h

/-- `w²` is pointwise dominated by the slot weight `slotW α a` on the open quadrant. -/
theorem w_sq_le_slotW (α : ℝ) (hα : 0 < α) {a : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : (Work.Spaces.w z) ^ 2 ≤ slotW α a z θ := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [slotW_zero_eq α hθ]
    simpa using mul_le_mul_of_nonneg_left (one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
      (sq_nonneg (Work.Spaces.w z))
  · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [slotW_of_pos_eq α h1 hθ]
    have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    simpa using mul_le_mul_of_nonneg_left (one_le_rpow_neg hgam hθ)
      (sq_nonneg (Work.Spaces.w z))

/-- `leafEta` is dominated by the slot weight `slotW α a` for every `a`. -/
theorem leafEta_le_slotW (α : ℝ) (hα : 0 < α) {a : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : leafEta z θ ≤ slotW α a z θ := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha; rw [leafEta, slotW_zero_eq α hθ]
  · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [leafEta, slotW_of_pos_eq α h1 hθ]
    exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _)

/-- `leafOne` is dominated by the slot weight `slotW α a` for every `a`. -/
theorem leafOne_le_slotW (α : ℝ) (hα : 0 < α) {a : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : leafOne z θ ≤ slotW α a z θ := by
  rw [leafOne]
  exact w_sq_le_slotW α hα hθ

/-- **The leaf weights of `IP4` for the slot with `a` angular derivatives**: `leafEta` and
`leafOne` for every slot, and `leafGam α` only for slots with `a ≥ 1` (the `σ^{-γ}`-term of
`H1IP` acts on `D_θ f`, which raises the number of angular derivatives by one).

The `a ≥ 1` guard is *essential*: the earlier `IsLeafW α ρ` (independent of `a`) was refuted by
the agent of `t2SlotRepaired` — at the slot `(a,b) = (0,4)` the weight `w²σ^{-γ}` is not the
slot weight `slotW α 0 = w²σ^{-η}` of `HkIntegrand α 4`, and `HkSq α 4 g` does not control
`|∫∫ w²σ^{-γ}(D_z^5 g)(D_z^4g)|` (analysis and numerics in
`Submission/Work/FTS/TransportS/SlotT2/NOTES_t2SlotRepaired_FALSE.md` and `_t2slot/`).  Every
instance the intended use consumes has the `γ`-weight only at slots with `a ≥ 1`, where
`slotW α a = w²σ^{-γ}` is exactly the mixed-slot weight. -/
def IsLeafW (α : ℝ) (a : ℕ) (ρ : ℝ → ℝ → ℝ) : Prop :=
  ρ = leafEta ∨ ρ = leafOne ∨ (1 ≤ a ∧ ρ = leafGam α)

/-- `leafGam α` is the slot weight `slotW α a` for `a ≥ 1` on the open quadrant. -/
theorem leafGam_le_slotW (α : ℝ) (hα : 0 < α) {a : ℕ} (ha : 1 ≤ a) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : leafGam α z θ ≤ slotW α a z θ := by
  rw [leafGam, slotW_of_pos_eq α ha hθ]

/-- Every leaf weight of the slot `a` is nonnegative on the open quadrant and pointwise
dominated by the slot weight `slotW α a`. -/
theorem IsLeafW_le (α : ℝ) (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ} (h : IsLeafW α a ρ) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ ρ z θ) ∧
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → ρ z θ ≤ slotW α a z θ) := by
  rcases h with rfl | rfl | ⟨ha, rfl⟩
  · exact ⟨fun z θ _ hθ0 hθ1 => leafEta_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith, by linarith [hθ1, Real.pi_pos]⟩),
      fun z θ _ hθ0 hθ1 => leafEta_le_slotW α hα (show θ ∈ Set.Ioo (0 : ℝ) (π / 2) from
        ⟨hθ0, hθ1⟩)⟩
  · exact ⟨fun _ _ _ _ _ => leafOne_nonneg _ _, fun z θ _ hθ0 hθ1 =>
      leafOne_le_slotW α hα (show θ ∈ Set.Ioo (0 : ℝ) (π / 2) from ⟨hθ0, hθ1⟩)⟩
  · refine ⟨fun z θ _ hθ0 hθ1 => ?_, fun z θ _ hθ0 hθ1 => ?_⟩
    · exact leafGam_nonneg α (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith, by linarith [hθ1, Real.pi_pos]⟩)
    · exact leafGam_le_slotW α hα ha (show θ ∈ Set.Ioo (0 : ℝ) (π / 2) from ⟨hθ0, hθ1⟩)

/-- The sum of the absolute values of all slot pairings occurring in the unfolding of `IP4`:
over the fifteen slots `(a,b)` of `ℋ⁴` (`a + b ≤ 4`) and the three leaf weights. -/
def leafSum (α : ℝ) (u v : Fn) : ℝ :=
  ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
    (if a + b ≤ 4 then
      |slotPairing leafEta a b u v| + |slotPairing leafOne a b u v|
        + (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0)
    else 0)


/-! ## The per-slot transport bounds -/



/-! ## The slot domination of the concrete `IP4` -/

/-- **The algebraic content of `IP4_unfold`**: the coercive inner product `IP` is dominated by
`leafSum`, i.e. by the sum of the absolute values of its slot pairings with the *leaf* weights
of `H1IP` (each of them pointwise dominated by the slot weight `slotW α a` of the corresponding
slot, `IsLeafW_le`).

For `IP α = Work.FTS.CoercivityStep.IP4 α` this is the unfolding of the four induction steps
`HkIPStep 1 1` together with the four elementary terms of `H1IP`. -/
def SlotDomIP (α₂ K : ℝ) (IP : ℝ → Fn → Fn → ℝ) : Prop :=
  0 < K ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ u v : Fn,
    Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
    |IP α u v| ≤ K * leafSum α u v

end Work.FTS.TransportS
end
end
