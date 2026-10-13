import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Coercivity.Gam_jet_upper_zero
import Submission.Work.Coercivity.Gam_jet_upper_pi
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.pzIter_hKer_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Uniform-in-`α` sup bounds for the slots of the model coefficient `A`

The paper's fundamental model (Elgindi, Annals **194** (2021), §FundamentalModel) has the
self-similar vorticity profile

`F(z,θ) = α · (Γ(θ)/c(α)) · 2z/(1+z)²`,

whose radial part `2z/(1+z)²` and angular part `Γ(θ)/c(α)` separate.  This file proves the
two sup bounds that the persistence proof needs for the coefficient `A` of `F`:

* every `D_z`-iterate up to order `4` of the radial profile `z ↦ 2z/(1+z)²` is bounded on
  `[0,∞)` by an absolute constant (`zslot_supBound`, value `24000`);
* every `D_θ`-iterate up to order `4` of `θ ↦ Γ(θ)/c(α)` is bounded uniformly for
  `α ∈ (0,1]` and `θ ∈ [0,π/2]` (`thetaslot_supBound`).

Because `D_z` and `D_θ` act on the two variables separately, the mixed slots
`D_z^b D_θ^a` of the product are bounded by the product of the two bounds
(`DzIter_fstSep` is the separation identity), which is the content of
`acoef_gamCoef_slots_le`.

The `z`-part goes through the closed form of the derivatives of `hKer(z) = z/(1+z)²`
(`Work.Spaces.pzIter_hKer_bound`) plus the Stirling expansion of `D_z^b`
(`Work.Spaces.DzIter_le_of_pzIter`); the `θ`-part goes through the coefficient sequence
`Tfun` with `D_θ^{j+1}Γ = α · Tfun j α · Γ` (`Work.Spaces.dthU_Gam_le`) and the lower
bound `c(α) ≥ 1/10` (`Work.Spaces.c_bounds`).
-/

namespace Work.FTS.StrongPersist.L3Aux

/-! ## Separation of variables for `D_z` -/

/-- `D_z`-iterates of a separated product `(z,θ) ↦ C θ * B z` act on the `z`-factor alone.
(The proof is a direct induction: `D_z (C ⊗ B) = C ⊗ D_z B` because `D_z` differentiates
only in `z`, together with the unconditional `deriv_const_mul'`.) -/
theorem DzIter_fstSep (b : ℕ) (C B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z θ => C θ * B z) z θ
      = C θ * Work.Spaces.DzIter b (fun z _ => B z) z θ := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ]
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    have h1 : (fun z' => Work.Spaces.DzIter b (fun z θ => C θ * B z) z' θ)
        = (fun z' => C θ * Work.Spaces.DzIter b (fun z _ => B z) z' θ) := by
      funext z'; exact ih z'
    rw [h1, Work.Spaces.deriv_const_mul']
    ring

/-! ## The radial profile `z ↦ 2z/(1+z)²` -/

/-- The radial profile is smooth on `(-1,∞)`. -/
lemma contDiffOn_two_z_div :
    ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z) (Set.Ioi (-1)) := by fun_prop
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) := by fun_prop
  exact hnum.div hden (fun z hz => by
    have h : (0 : ℝ) < 1 + z := by have := Set.mem_Ioi.mp hz; linarith
    positivity)

/-- The `z`-derivatives of the profile `2z/(1+z)²` are twice those of `hKer`. -/
lemma pzIter_two_z_div (j : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ
      = 2 * deriv^[j] Work.Spaces.hKer z := by
  have hfun : (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2)
      = (fun z θ => (fun _ => (2 : ℝ)) θ * Work.Spaces.hKer z) := by
    funext z θ; simp only [Work.Spaces.hKer_apply]; ring
  rw [hfun, Work.Spaces.pzIter_decomp]

/-- The weighted derivative bound for `hKer`: `|z^j ∂_z^j hKer z| ≤ j!(j+1)` for `z ≥ 0`.
This is `Work.Spaces.pzIter_hKer_bound` with the weight `(1+z)^j` replaced by `z^j` (the
ratio `z/(1+z)` lies in `[0,1]`). -/
lemma deriv_hKer_zpow_le (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ j * deriv^[j] Work.Spaces.hKer z| ≤ (j.factorial : ℝ) * (j + 1) := by
  have hz1 : (1 + z) ≠ 0 := by positivity
  have h1 : z ^ j = (z / (1 + z)) ^ j * (1 + z) ^ j := by
    rw [← mul_pow, div_mul_cancel₀ z hz1]
  have hq0 : (0 : ℝ) ≤ z / (1 + z) := div_nonneg hz (by linarith)
  have hq1 : z / (1 + z) ≤ 1 := by
    rw [div_le_one (by linarith : (0 : ℝ) < 1 + z)]; linarith
  have hq : |(z / (1 + z)) ^ j| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hq0 j)]
    exact pow_le_one₀ hq0 hq1
  have h2 : |(1 + z) ^ j * deriv^[j] Work.Spaces.hKer z| ≤ (j.factorial : ℝ) * (j + 1) := by
    rw [show (1 + z) ^ j = (z + 1) ^ j by ring]
    exact Work.Spaces.pzIter_hKer_bound j z hz
  rw [h1, mul_assoc, abs_mul]
  calc |(z / (1 + z)) ^ j| * |(1 + z) ^ j * deriv^[j] Work.Spaces.hKer z|
      ≤ 1 * ((j.factorial : ℝ) * (j + 1)) :=
        mul_le_mul hq h2 (abs_nonneg _) (by norm_num)
    _ = (j.factorial : ℝ) * (j + 1) := one_mul _

/-- The all-orders bound for the weighted `z`-derivatives of the profile:
`|z^j ∂_z^j (2z/(1+z)²)| ≤ 2 j!(j+1)`. -/
lemma zpow_pzIter_two_z_div_le (j : ℕ) {z : ℝ} (hz : 0 ≤ z) (θ : ℝ) :
    |z ^ j * Work.Spaces.pzIter j (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ|
      ≤ 2 * ((j.factorial : ℝ) * (j + 1)) := by
  rw [pzIter_two_z_div]
  rw [show z ^ j * (2 * deriv^[j] Work.Spaces.hKer z)
        = 2 * (z ^ j * deriv^[j] Work.Spaces.hKer z) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have := deriv_hKer_zpow_le j hz
  linarith

/-- **The `z`-slots of the radial profile.**  Every `D_z`-iterate of order `b ≤ 4` of
`z ↦ 2z/(1+z)²` is bounded by `24000` on `[0,∞)`. -/
lemma zslot_supBound : ∀ b ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.DzIter b (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ| ≤ 24000 := by
  intro b hb z hz θ hθ
  have hsmooth := fun (θ' : ℝ) (_ : θ' ∈ Work.Spaces.Iθ) => contDiffOn_two_z_div
  have hbound : ∀ j ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ j * Work.Spaces.pzIter j (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z θ| ≤ 240 := by
    intro j hj z hz θ hθ
    have h1 := zpow_pzIter_two_z_div_le j hz θ
    have h2 : (j.factorial : ℝ) * (j + 1) ≤ 120 := by interval_cases j <;> norm_num
    linarith
  have hmain := Work.Spaces.DzIter_le_of_pzIter
    (h := fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) (M := 240) (by norm_num)
    hsmooth hbound b hb z hz θ hθ
  linarith

/-! ## The angular profile `θ ↦ Γ(θ)/c(α)` -/

/-- **The `θ`-slots of the angular profile.**  Every `D_θ`-iterate of order `a ≤ 4` of
`Γ(θ)/c(α)` is bounded uniformly in `α ∈ (0,1]` and `θ ∈ [0,π/2]`.  The bound is
`10 · (1 + ∑_{j<4} tBound j 0)`: the factor `1/c(α)` is at most `10` (`c_bounds`), while
`D_θ^a Γ = α · Tfun (a-1) α · Γ` (`dthU_Gam_le`) is at most `tBound (a-1) 0` since
`α ≤ 1` and `Γ ≤ 1`. -/
lemma thetaslot_supBound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ a ≤ 4,
    ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[a] (fun θ => Work.Spaces.Gam α θ / Work.Spaces.c α) θ| ≤ K := by
  refine ⟨10 * (1 + ∑ j ∈ Finset.range 4, Work.Spaces.tBound j 0), ?_, ?_⟩
  · have hSnn : 0 ≤ ∑ j ∈ Finset.range 4, Work.Spaces.tBound j 0 :=
      Finset.sum_nonneg fun j _ => Work.Spaces.tBound_nonneg j 0
    linarith
  · intro α hα hα1 a ha θ hθ
    have hc := Work.Spaces.c_bounds α hα hα1
    have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
    have hcinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/10) hc.1
      have h10 : (1 : ℝ) / (1/10) = 10 := by norm_num
      rw [h10] at h
      simpa using h
    have hSnn : 0 ≤ ∑ j ∈ Finset.range 4, Work.Spaces.tBound j 0 :=
      Finset.sum_nonneg fun j _ => Work.Spaces.tBound_nonneg j 0
    have hconst : Work.Spaces.dthU^[a] (fun θ => Work.Spaces.Gam α θ / Work.Spaces.c α)
        = fun θ => (Work.Spaces.c α)⁻¹
            * Work.Spaces.dthU^[a] (fun θ => Work.Spaces.Gam α θ) θ := by
      rw [show (fun θ => Work.Spaces.Gam α θ / Work.Spaces.c α)
            = (fun θ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α θ) from by
              funext θ; rw [div_eq_inv_mul]]
      exact Work.Spaces.dthU_iter_const_mul a (Work.Spaces.c α)⁻¹
        (fun θ => Work.Spaces.Gam α θ)
    rw [hconst, abs_mul, abs_of_nonneg (inv_nonneg.mpr hcpos.le)]
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      have h1 : |Work.Spaces.dthU^[0] (fun θ => Work.Spaces.Gam α θ) θ| ≤ 1 := by
        rw [show Work.Spaces.dthU^[0] (fun θ => Work.Spaces.Gam α θ) θ
              = Work.Spaces.Gam α θ by simp, abs_of_nonneg hG.1]
        exact hG.2
      calc (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[0] (fun θ => Work.Spaces.Gam α θ) θ|
          ≤ 10 * 1 := mul_le_mul hcinv h1 (abs_nonneg _) (by norm_num)
        _ ≤ 10 * (1 + ∑ j ∈ Finset.range 4, Work.Spaces.tBound j 0) := by linarith
    · have hle := Work.Spaces.dthU_Gam_le a hpos α hα hα1 θ hθ
      have htb : 0 ≤ Work.Spaces.tBound (a-1) 0 := Work.Spaces.tBound_nonneg _ _
      have h1 : |Work.Spaces.dthU^[a] (fun θ => Work.Spaces.Gam α θ) θ|
          ≤ Work.Spaces.tBound (a-1) 0 := by
        refine hle.trans ?_
        have h2 : α * Work.Spaces.tBound (a-1) 0 ≤ Work.Spaces.tBound (a-1) 0 :=
          mul_le_of_le_one_left htb hα1
        calc α * Work.Spaces.tBound (a-1) 0 * Work.Spaces.Gam α θ
            ≤ Work.Spaces.tBound (a-1) 0 * 1 :=
              mul_le_mul h2 hG.2 hG.1 (by linarith)
          _ = Work.Spaces.tBound (a-1) 0 := mul_one _
      have hmem : a - 1 ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
      have htbS : Work.Spaces.tBound (a-1) 0
          ≤ ∑ j ∈ Finset.range 4, Work.Spaces.tBound j 0 :=
        Finset.single_le_sum (f := fun j => Work.Spaces.tBound j 0)
          (fun j _ => Work.Spaces.tBound_nonneg j 0) hmem
      calc (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[a] (fun θ => Work.Spaces.Gam α θ) θ|
          ≤ 10 * Work.Spaces.tBound (a-1) 0 :=
            mul_le_mul hcinv h1 (abs_nonneg _) (by norm_num)
        _ ≤ 10 * (1 + ∑ j ∈ Finset.range 4, Work.Spaces.tBound j 0) := by linarith

/-! ## The mixed slots of the coefficient `A` -/

theorem acoef_gamCoef_slots_le : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    (∀ b ≤ 4, ∀ z ∈ Work.Spaces.Iz,
      |Work.Spaces.DzIter b (fun z _ => 2 * z / (1 + z) ^ 2) z 0| ≤ K) ∧
    (∀ a b : ℕ, a + b ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.mixed b a
        (fun z θ => (2 * z / (1 + z) ^ 2)
          * (Work.Spaces.Gam α θ / Work.Spaces.c α)) z θ| ≤ K) := by
  obtain ⟨K2, hK2pos, hK2⟩ := thetaslot_supBound
  refine ⟨24000 * K2 + 24000 + 1, by nlinarith [hK2pos], ?_⟩
  intro α hα hα1
  constructor
  · intro b hb z hz
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ :=
      ⟨le_refl 0, by have := Real.pi_pos; linarith⟩
    have h := zslot_supBound b hb z hz 0 h0
    nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 24000) hK2pos.le]
  · intro a b hab z hz θ hθ
    have ha : a ≤ 4 := by omega
    have hb : b ≤ 4 := by omega
    set A : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ / Work.Spaces.c α with hA
    set B : ℝ → ℝ := fun z => 2 * z / (1 + z) ^ 2 with hB
    have hf : (fun z θ => (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ / Work.Spaces.c α))
        = fun z θ => A θ * B z := by
      funext z θ; simp only [A, B]; ring
    have hDth : Work.Spaces.DthIter a (fun z θ => A θ * B z)
        = fun z θ => Work.Spaces.dthU^[a] A θ * B z := by
      funext z θ
      exact Work.Spaces.DthIter_decomp a A B z θ
    have hmix : Work.Spaces.mixed b a
          (fun z θ => (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ / Work.Spaces.c α)) z θ
        = Work.Spaces.dthU^[a] A θ * Work.Spaces.DzIter b (fun z _ => B z) z θ := by
      show Work.Spaces.DzIter b (Work.Spaces.DthIter a
        (fun z θ => (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ / Work.Spaces.c α))) z θ = _
      rw [hf, hDth]
      exact DzIter_fstSep b (fun θ => Work.Spaces.dthU^[a] A θ) B z θ
    rw [hmix, abs_mul]
    calc |Work.Spaces.dthU^[a] A θ| * |Work.Spaces.DzIter b (fun z _ => B z) z θ|
        ≤ K2 * 24000 :=
          mul_le_mul (hK2 α hα hα1 a ha θ hθ) (zslot_supBound b hb z hz θ hθ)
            (abs_nonneg _) hK2pos.le
      _ ≤ 24000 * K2 + 24000 + 1 := by
          nlinarith [hK2pos, mul_nonneg (by norm_num : (0:ℝ) ≤ 24000) hK2pos.le]

end Work.FTS.StrongPersist.L3Aux
