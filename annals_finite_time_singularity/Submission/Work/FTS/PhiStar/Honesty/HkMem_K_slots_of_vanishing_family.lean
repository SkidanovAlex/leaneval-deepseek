import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.HkMem_seven_slots_of_vanishing_family
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.VanGridK
import Submission.Work.FTS.PhiStar.Honesty.vanGridK_integrable
import Submission.Work.FTS.PhiStar.Honesty.HkIntegrand_K_le_of_bounds
import Submission.Work.FTS.PhiStar.Honesty.HkIntegrand_zero_DzIter_zsqPz2_le_K
import Submission.Work.FTS.PhiStar.Honesty.vig_zsqPz2_le_K
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The general-level (`K`) honesty transfer for the three elliptic slots

This file proves `Work.FTS.PhiStar.Honesty.HkMem_K_slots_of_vanishing_family`: the level-`K`
generalisation of `Work.FTS.ClassC.HkMem_seven_slots_of_vanishing_family`.  For a datum `Ψ`
which is `C^∞` on the open quadrant, whose *pure radial* slots `D_z^l ∂_θ^m Ψ` (`l ≤ K + 2`,
`m ≤ 2`) are honestly in `ℋ⁰` (singular `η`-weight), and whose angular slots of order
`3 ≤ t ≤ K + 2` are integrable against the *vanishing* weights `sin(2θ)^{2t-4-γ}`, the three
derivatives

  `z²∂_z²Ψ`,   `∂_θ²Ψ`,   `z∂_z∂_θ²Ψ`

lie in `ℋ^K`.

The proof has the same layers as the level-`7` instance:

1. the grid majorant `vanGridK α Ψ K` (`Submission.Work.FTS.PhiStar.Honesty.VanGridK`) and its
   integrability `vanGridK_integrable` from the two families `hσ`, `hV`;
2. the per-slot domination `HkIntegrand_K_le_of_bounds` — the arithmetic re-sum of the pointwise
   reduction `HkIntegrand_le_pure_vanishing`, using that every pure slot and every vanishing
   slot is `≤ 4 · vanGridK`;
3. the six per-slot bounds (the `z²∂_z²Ψ` pair is delegated, the other four are proved below);
4. the assembly `HkMem_K_of_gridK` via `HkMem_of_majorant_ae`.
-/

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory

/-! ## The four remaining per-slot bounds -/

/-- The pure-`z` slot `HkIntegrand α 0 (D_z^j ∂_θ²Ψ)`, `j ≤ K`, is the summand
`(l,m) = (j,2)` of the first block of the grid majorant, hence dominated by `4 · vanGridK`. -/
theorem HkIntegrand_zero_DzIter_pthIter_two_le_K {α : ℝ} {K : ℕ}
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) z θ
        ≤ 4 * vanGridK α Ψ K z θ := by
  intro j _hj z _hz θ hθ
  have hmem := hkIntegrand_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (r := 2) (l := j)
    (by norm_num) (by omega) z θ hθ
  have hnn : 0 ≤ vanGridK α Ψ K z θ := vanGridK_nonneg α Ψ K z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  linarith

/-- The vanishing slot of `∂_θ²Ψ` is *literally* the `(t,l) = (r+2, j)` summand of the grid
majorant, because `∂_θ^r∂_θ²Ψ = ∂_θ^{r+2}Ψ` and `2(r+2) - 4 - γ = 2r - γ`. -/
theorem vig_pthIter_two_le_K {α : ℝ} {K : ℕ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α (Work.Spaces.pthIter 2 Ψ) r j z θ
        ≤ 4 * vanGridK α Ψ K z θ := by
  intro j r _hr _hrj z _hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h2 : Work.FTS.ClassC.vig α (Work.Spaces.pthIter 2 Ψ) r j
      = Work.FTS.ClassC.hVint α Ψ (r + 2) j := by
    funext z' θ'
    rw [Work.FTS.ClassC.vig, Work.FTS.ClassC.hVint,
      show Work.Spaces.pthIter r (Work.Spaces.pthIter 2 Ψ)
        = Work.Spaces.pthIter (r + 2) Ψ from
        (Work.FTS.ClassC.seven_pthIter_add r 2 Ψ).symm]
    congr 2
    push_cast
    ring
  rw [h2]
  have h1 := hVint_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (t := r + 2) (l := j)
    (by omega) (by omega) (by omega) z θ hθ
  have h2' : 0 ≤ vanGridK α Ψ K z θ := vanGridK_nonneg α Ψ K z hθI
  linarith

/-- `D_z^j` composed with one further `D_z` is `D_z^{j+1}`. -/
private theorem DzIter_Dz_eq_aux_K (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz f) = Work.Spaces.DzIter (j + 1) f := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ (n := n) (f := Work.Spaces.Dz f), ih,
        ← Work.Spaces.DzIter_succ (n := n + 1) (f := f)]

/-- The pure-`z` slot `HkIntegrand α 0 (D_z^j (z ∂_z∂_θ²Ψ))` is the summand `(l,m) = (j+1,2)`
of the first block of the grid majorant (`z ∂_z∂_θ²Ψ = D_z∂_θ²Ψ`). -/
theorem HkIntegrand_zero_DzIter_Dz_pthIter_two_le_K {α : ℝ} {K : ℕ}
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter j
            (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) z θ
        ≤ 4 * vanGridK α Ψ K z θ := by
  intro j _hj z _hz θ hθ
  have harg : Work.Spaces.DzIter j
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 Ψ) :=
    DzIter_Dz_eq_aux_K j (Work.Spaces.pthIter 2 Ψ)
  rw [harg]
  have hmem := hkIntegrand_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (r := 2) (l := j + 1)
    (by norm_num) (by omega) z θ hθ
  have hnn : 0 ≤ vanGridK α Ψ K z θ := vanGridK_nonneg α Ψ K z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  linarith

/-- The vanishing slot of `z ∂_z∂_θ²Ψ = D_z∂_θ²Ψ`: on the open quadrant
`∂_θ^r(D_z∂_θ²Ψ) = D_z∂_θ^{r+2}Ψ`, so the slot is *literally* `hVint α Ψ (r+2) (j+1)`, a
summand of the grid majorant. -/
theorem vig_Dz_pthIter_two_le_K {α : ℝ} {K : ℕ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α
          (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) r j z θ
        ≤ 4 * vanGridK α Ψ K z θ := by
  intro j r hr _hrj z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- `∂_θ^r (z ∂_z∂_θ²Ψ) = D_z ∂_θ^{r+2}Ψ` on the open quadrant
  have hcongr : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter r (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ
        = Work.Spaces.DzIter 1 (Work.Spaces.pthIter (r + 2) Ψ) z θ := by
    intro z' θ' hz' hθ' hπ'
    have h0 := Work.FTS.ClassC.seven_pthIter_DzIter_eqOn_Q0
      (f := Work.Spaces.pthIter 2 Ψ) (Work.FTS.ClassC.SmoothOpen_pthIter_classC hΨ 2) r 1
      z' θ' hz' hθ' hπ'
    rw [← Work.FTS.ClassC.seven_pthIter_add r 2 Ψ] at h0
    exact h0
  have hD : Work.Spaces.DzIter j
        (Work.Spaces.pthIter r
          (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter (r + 2) Ψ) z θ := by
    have h2 := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.pthIter r
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ))
      (G := Work.Spaces.DzIter 1 (Work.Spaces.pthIter (r + 2) Ψ)) hcongr j z θ hz hθ.1 hθ.2
    rw [h2, Work.FTS.ClassC.seven_DzIter_add j 1 (Work.Spaces.pthIter (r + 2) Ψ)]
  have heq : Work.FTS.ClassC.vig α
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) r j z θ
      = Work.FTS.ClassC.hVint α Ψ (r + 2) (j + 1) z θ := by
    simp only [Work.FTS.ClassC.vig, Work.FTS.ClassC.hVint]
    rw [hD]
    have hexp : 2 * ((r + 2 : ℕ) : ℝ) - 4 - Work.Spaces.gam α
        = 2 * (r : ℝ) - Work.Spaces.gam α := by
      push_cast
      ring
    rw [hexp]
  rw [heq]
  have h1 := hVint_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (t := r + 2) (l := j + 1)
    (by omega) (by omega) (by omega) z θ hθ
  have h2' : 0 ≤ vanGridK α Ψ K z θ := vanGridK_nonneg α Ψ K z hθI
  linarith

/-! ## The assembly engine -/

/-- **The assembly step.**  If the grid majorant `vanGridK α Ψ K` is integrable on the angular
interval and in the outer `z`-variable, and if for a function `f` (smooth on the open quadrant)
every pure radial level-`0` slot and every vanishing-weight angular slot of level `K` is
dominated on the open quadrant by `4 · vanGridK α Ψ K`, then `f ∈ ℋ^K`. -/
theorem HkMem_K_of_gridK {α : ℝ} {K : ℕ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ f : ℝ → ℝ → ℝ}
    (hG : (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => vanGridK α Ψ K z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          vanGridK α Ψ K z θ) Work.Spaces.Iz)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (h0 : ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ ≤ 4 * vanGridK α Ψ K z θ)
    (h1 : ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α f r j z θ ≤ 4 * vanGridK α Ψ K z θ) :
    Work.Spaces.HkMem α K f := by
  set C : ℝ := 4 * ((K : ℝ) + 1)
    + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K with hC
  have hLnn : 0 ≤ C := by
    rw [hC]
    have hv := Work.FTS.ClassC.vanSum_nonneg α hα hγ f hsm K
    have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith
  refine Work.FTS.EllipticEst.HkMem_of_majorant_ae
    (M := fun z θ => C * vanGridK α Ψ K z θ)
    α K (hsm.continuousOn_HkIntegrand α K) ?_ ?_ ?_
  · intro z hz
    exact (hG.1 z hz).const_mul C
  · refine MeasureTheory.IntegrableOn.congr_fun (hG.2.const_mul C) (fun z _ => ?_)
      measurableSet_Ici
    exact (MeasureTheory.integral_const_mul C _).symm
  · intro z hz
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [Work.FTS.LocData.HkIntegrand_zero_fst]
      exact mul_nonneg hLnn
        (vanGridK_nonneg α Ψ K 0 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    · exact HkIntegrand_K_le_of_bounds hα hγ hsm
        (fun z θ hθ' => vanGridK_nonneg α Ψ K z ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩)
        h0 h1 hzpos hθ

/-! ## The target -/

theorem HkMem_K_slots_of_vanishing_family (K : ℕ) {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hσ : ∀ l m : ℕ, l ≤ K + 2 → m ≤ 2 →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)))
    (hV : ∀ t l : ℕ, 3 ≤ t → t ≤ K + 2 → l ≤ K + 2 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz) :
    Work.Spaces.HkMem α K (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
      Work.Spaces.HkMem α K (Work.Spaces.pthIter 2 Ψ) ∧
      Work.Spaces.HkMem α K (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) := by
  have hG := vanGridK_integrable (α := α) (K := K) (Ψ := Ψ) hσ hV
  refine ⟨?_, ?_, ?_⟩
  · -- conjunct 1: the smoothing family `z²∂_z²Ψ`
    exact HkMem_K_of_gridK hα hγ hG ((hΨ.pzIter 2).zsq_mul)
      (fun j hj => HkIntegrand_zero_DzIter_zsqPz2_le_K hγ hΨ j hj)
      (fun j r hr hrj => vig_zsqPz2_le_K hγ hΨ j r hr hrj)
  · -- conjunct 2: `∂_θ²Ψ`
    exact HkMem_K_of_gridK hα hγ hG
      (Work.FTS.ClassC.SmoothOpen_pthIter_classC hΨ 2)
      (fun j hj => HkIntegrand_zero_DzIter_pthIter_two_le_K hγ hΨ j hj)
      (fun j r hr hrj => vig_pthIter_two_le_K hγ hΨ j r hr hrj)
  · -- conjunct 3: `z ∂_z∂_θ²Ψ = D_z∂_θ²Ψ`
    exact HkMem_K_of_gridK hα hγ hG
      ((Work.FTS.ClassC.SmoothOpen_pthIter_classC hΨ 2).Dz)
      (fun j hj => HkIntegrand_zero_DzIter_Dz_pthIter_two_le_K hγ hΨ j hj)
      (fun j r hr hrj => vig_Dz_pthIter_two_le_K hγ hΨ j r hr hrj)

end Work.FTS.PhiStar.Honesty
