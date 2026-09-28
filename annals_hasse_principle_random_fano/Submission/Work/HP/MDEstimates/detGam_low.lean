import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.det_gam_gen
import Submission.Work.HP.EE.wedgeNorm_veronese
import Submission.Work.HP.EEupper.gcdMinors_veronese
import Submission.Work.HP.Sig2.nu_indep

/-!
# Lower bound for `det Γ_{x,y}`

The lower bound in Browning--Le Boudec--Sawin, "Lemma upper and lower bounds det": for `2 ≤ d`
and `d ≤ n` there is `C > 0` with

`𝔡₂(x,y) ‖x‖^{d-1} ‖y‖^{d-1} ≤ C · detL (Λ_{ν(x)} ∩ Λ_{ν(y)})`

for all primitive, `ℤ`-linearly independent `x, y : ℤ^{n+1}`.

By `Work.HP.det_gam_gen` both the minimal rank-`2` determinant `dmin 2 {x,y}` and the covolume
`detL (latOrth c ⊓ latOrth d)` equal `wedgeNorm c d / 𝒢(c,d)`, where
`wedgeNorm c d = √(‖c‖²‖d‖² - ⟨c,d⟩²)` is the Plücker norm and `𝒢 = gcdMinors2` the gcd of the
`2 × 2` minors.  Lemma G (`Work.HP.EEupper.gcdMinors_veronese`) replaces
`𝒢(ν(x),ν(y))` by `𝒢(x,y)`, so the two `𝒢`'s cancel and the claim reduces to the angular bound
`‖ν(x)∧ν(y)‖ ≥ c ‖x‖^{d-1}‖y‖^{d-1}‖x∧y‖` of `Work.HP.EE.wedgeNorm_veronese`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

theorem detGam_low (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Fin (n + 1) → ℤ, Work.HP.IsPrim x → Work.HP.IsPrim y →
      LinearIndependent ℤ ![x, y] →
      Work.HP.dmin 2 {x, y} * Work.HP.eNorm x ^ (d - 1) * Work.HP.eNorm y ^ (d - 1)
        ≤ C * Work.HP.detL (Work.HP.Gam d n x y) := by
  obtain ⟨c, hcpos, hc⟩ := EE.wedgeNorm_veronese d n hd
  refine ⟨c⁻¹, inv_pos.mpr hcpos, ?_⟩
  intro x y hx hy hxy
  -- `ℤ`-independence forces `x ≠ ±y`
  have hne1 : x ≠ y := by
    intro h
    have h0 : (1 : ℤ) • x + (-1 : ℤ) • y = 0 := by rw [h]; simp
    exact one_ne_zero (LinearIndependent.pair_iff.mp hxy 1 (-1) h0).1
  have hne2 : x ≠ -y := by
    intro h
    have h0 : (1 : ℤ) • x + (1 : ℤ) • y = 0 := by rw [h]; simp
    exact one_ne_zero (LinearIndependent.pair_iff.mp hxy 1 1 h0).1
  -- the Veronese pair is independent, and Lemma G identifies the two gcds of minors
  have hnu : LinearIndependent ℤ ![veronese d n x, veronese d n y] :=
    Sig2.nu_indep d n hd x y hx hy hne1 hne2
  have hG : gcdMinors2 (veronese d n x) (veronese d n y) = gcdMinors2 x y :=
    Work.HP.EEupper.gcdMinors_veronese d n (by omega) x y hx hy
  -- the two exact determinant formulas
  have hdet : detL (Gam d n x y) =
      wedgeNorm (veronese d n x) (veronese d n y) / (gcdMinors2 x y : ℝ) := by
    rw [show Gam d n x y = latOrth (veronese d n x) ⊓ latOrth (veronese d n y) from rfl,
      (det_gam_gen (veronese d n x) (veronese d n y) hnu).1, hG]
  have hdmin : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) =
      wedgeNorm x y / (gcdMinors2 x y : ℝ) := by
    rw [(det_gam_gen x y hxy).2, (det_gam_gen x y hxy).1]
  have hgpos : 0 < (gcdMinors2 x y : ℝ) := by
    exact_mod_cast Work.HP.DGG.gcdMinors2_pos x y hxy
  -- the angular bound, in the shape of the target
  have hW : eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y
      ≤ c⁻¹ * wedgeNorm (veronese d n x) (veronese d n y) := by
    have h1 : c * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y)
        ≤ wedgeNorm (veronese d n x) (veronese d n y) := by
      have h := hc x y
      have heq : c * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y)
          = c * eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y := by ring
      rw [heq]; exact h
    calc eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y
        = c⁻¹ * (c * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y)) := by
          field_simp
      _ ≤ c⁻¹ * wedgeNorm (veronese d n x) (veronese d n y) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hcpos))
  rw [hdmin, hdet, div_eq_mul_inv, div_eq_mul_inv]
  calc wedgeNorm x y * (gcdMinors2 x y : ℝ)⁻¹ * eNorm x ^ (d - 1) * eNorm y ^ (d - 1)
      = (gcdMinors2 x y : ℝ)⁻¹ * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y) := by
        ring
    _ ≤ (gcdMinors2 x y : ℝ)⁻¹ * (c⁻¹ * wedgeNorm (veronese d n x) (veronese d n y)) :=
        mul_le_mul_of_nonneg_left hW (inv_nonneg.mpr (le_of_lt hgpos))
    _ = c⁻¹ * (wedgeNorm (veronese d n x) (veronese d n y) * (gcdMinors2 x y : ℝ)⁻¹) := by
        ring

end Work.HP.MDEstimates
