import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseGateFS.HonRowsDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.honE_count_PL` — the `count_PL` row at the honest model

FS's low-momentum cut-off `f_L` vanishes off `2K_L√(μa)` (`honE_fL_supp2`, the
F7-repaired support at the *honest* `LowCut` profile), so the excited modes `s`
with `f_L s ≠ 0` have lattice labels `labVec N s` whose momenta `2π·labVec N s
= ℓ·kmom s` lie in the ball of radius `2ℓK_L√(μa) = 2K_ℓK_L` (`honE_ellKL`).
The lattice-ball count `Work.BoseK15.card_le_of_vec_norm_le` then bounds the
number of such labels by `(2K_ℓK_L/π + 1)³`, and `2·K_ℓK_L/π + 1 ≤ 2·K_ℓK_L`
for `K_ℓK_L ≥ 1` gives the bound `8(K_ℓK_L)³ ≤ K₀(K_ℓK_L)³`.

This is the `count_PL` row of `HonestRows` (`HonestRowsAssemble.lean`), needed by
the `Est1` chapter to bound the number of summands of the low-momentum part of
`Q₃`.
-/

namespace Work.BoseGateFS

open scoped BigOperators Pointwise Real

/-- `ZMod.valMinAbs` is injective, so the centred integer label vector determines
the cube mode.  (Local copy: the `BoseBoxFock` instances of this lemma are not in
this module's import cone.) -/
private lemma labVec_inj (N : ℕ) : Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro a b h
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun h i)

theorem honE_count_PL {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ}
    (S : Work.BoseGateFS.HonSetup v h fc fu HM μ) {K₀ : ℝ} (hK : 8 ≤ K₀)
    (hKL : 1 ≤ (Work.BoseGateFS.honE v h fc fu HM μ).Kl
      * (Work.BoseGateFS.honE v h fc fu HM μ).KL) :
    (((Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
        (fun s => (Work.BoseGateFS.honE v h fc fu HM μ).fL s ≠ 0)).card : ℝ)
      ≤ K₀ * ((Work.BoseGateFS.honE v h fc fu HM μ).Kl
          * (Work.BoseGateFS.honE v h fc fu HM μ).KL) ^ 3 := by
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hell := honE_ellKL S
  -- the supported modes, and the lattice radius `ρ = K_ℓK_L`
  set T : Finset (Work.BoseBoxFock.Lab (HM μ).N) :=
    (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
      (fun s => (honE v h fc fu HM μ).fL s ≠ 0) with hT
  set ρ : ℝ := (honE v h fc fu HM μ).Kl * (honE v h fc fu HM μ).KL with hρ
  have hρpos : 0 < ρ := lt_of_lt_of_le one_pos hKL
  -- the lattice labels of the supported modes sit in the ball of radius `2ρ`
  have hsupp : ∀ n ∈ T.image (Work.BoseBoxFock.labVec (HM μ).N),
      ‖Work.BoseB4.vec n‖ ≤ 2 * ρ := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨s, hs, rfl⟩ := hn
    rw [hT, Finset.mem_filter] at hs
    obtain ⟨-, hsfL⟩ := hs
    have h1 : ‖(honF v h fc fu HM μ).kmom s‖ ≤ 2 * ((honE v h fc fu HM μ).KL
        * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)) :=
      honE_fL_supp2 S s hsfL
    have h2 : (honF v h fc fu HM μ).kmom s
        = (Work.BoseBoxFock.ellH v μ)⁻¹ •
            Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N s) := by
      rw [honF_kmom]
      rfl
    have h3 : ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N s)‖
        = Work.BoseBoxFock.ellH v μ * ‖(honF v h fc fu HM μ).kmom s‖ := by
      rw [h2, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓpos]
      field_simp
    have h4 : Work.BoseBoxFock.ellH v μ * (2 * ((honE v h fc fu HM μ).KL
        * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)))
        = 2 * ρ := by
      have hell' : Work.BoseBoxFock.ellH v μ * ((honE v h fc fu HM μ).KL
          * Real.sqrt ((honE v h fc fu HM μ).mu
              * (honE v h fc fu HM μ).aScat)) = ρ := by
        rw [← honE_ell S, hρ, ← mul_assoc]
        exact hell
      rw [← hell']
      ring
    calc ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N s)‖
        = Work.BoseBoxFock.ellH v μ * ‖(honF v h fc fu HM μ).kmom s‖ := h3
      _ ≤ Work.BoseBoxFock.ellH v μ * (2 * ((honE v h fc fu HM μ).KL
            * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))) :=
          mul_le_mul_of_nonneg_left h1 hℓpos.le
      _ = 2 * ρ := h4
  -- the lattice ball count
  have hcard : (T.card : ℝ) ≤ (2 * ρ / Real.pi + 1) ^ 3 := by
    have hcount := Work.BoseK15.card_le_of_vec_norm_le
      (T.image (Work.BoseBoxFock.labVec (HM μ).N)) (2 * ρ)
      (by have h2 : (0 : ℝ) < 2 * ρ := mul_pos (by norm_num) hρpos; linarith) hsupp
    rwa [Finset.card_image_of_injective T (labVec_inj (HM μ).N)] at hcount
  have hfinal : (2 * ρ / Real.pi + 1) ^ 3 ≤ K₀ * ρ ^ 3 := by
    have hπ : (2 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
    have hstep : 2 * ρ / Real.pi + 1 ≤ 2 * ρ := by
      have h1 : 2 * ρ / Real.pi ≤ ρ := by
        rw [div_le_iff₀ Real.pi_pos]
        nlinarith
      linarith
    have hnn : (0 : ℝ) ≤ 2 * ρ / Real.pi + 1 := by
      have h2 : (0 : ℝ) < 2 * ρ := mul_pos (by norm_num) hρpos
      have h3 : (0 : ℝ) < 2 * ρ / Real.pi := div_pos h2 Real.pi_pos
      linarith
    calc (2 * ρ / Real.pi + 1) ^ 3 ≤ (2 * ρ) ^ 3 := pow_le_pow_left₀ hnn hstep 3
      _ = 8 * ρ ^ 3 := by ring
      _ ≤ K₀ * ρ ^ 3 := by
          have hρ3 : (0 : ℝ) ≤ ρ ^ 3 := by positivity
          nlinarith
  linarith

end Work.BoseGateFS
