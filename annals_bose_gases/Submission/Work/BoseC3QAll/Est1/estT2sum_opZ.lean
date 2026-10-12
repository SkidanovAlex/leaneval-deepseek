import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.OpZ_Atil_sum
import Submission.Work.BoseC3QAll.Est1.OpZ_Bterm
import Submission.Work.BoseC3QAll.Est1.OpZ_RE1
import Submission.Work.BoseC3QAll.Est1.OpZ_cD_bd
import Submission.Work.BoseC3QAll.Est1.OpZ_kappa
import Submission.Work.BoseC3QAll.Est1.OpZ_perK
import Submission.Work.BoseC3QAll.Est1.OpZ_reserve
import Submission.Work.BoseC3QAll.absz_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.estT2sum_opZ` — the normal-ordered half of FS `T₂`

This is the `T₂,op` (`eq:T2opprime`) half of piece **B** of FS
`eq:EstimateQ3Tilde1`, in the physical normalisation `Z²·Σ_k c_k⁻¹`:

  `Z²Σ_{k∈P_H} c_k⁻¹ T2OpF k Φ ≤ C·e1A·‖Φ‖² + (b/400)⟨gapOpT⟩ + (𝓁²/8)⟨R_{P_H^q}⟩`,
  `Z = z/ℓ³`, `c_k = (1-𝓁²)𝒟_k`.

## The route (FS `eq:T2prime`→`eq:T2opprime`)

Write `A_{sk} = ã_s + β_{sk}ã_{-s}†`, `b_q = a_q + α_qa_{-q}†`, and

  `T2OpF k Φ = Σ_{s,s'} γ_{sk}γ_{s'k}·⟨b_{s'-k}(A_{sk}Φ), b_{s-k}(A_{s'k}Φ)⟩`,
  `γ_{sk} = gA E s k = f_L(s)Ŵ₁(k)q3Denom(s,k)`.

1. **Cauchy–Schwarz / AM–GM** in the Fock form (`bp_le_half`) collapses the bilinear
   form into `Σ_{s,s'}γ_{sk}γ_{s'k}‖b_{s'-k}(A_{sk}Φ)‖²` (the index swap of the
   symmetric double sum; `OpZ_perK`).
2. **Commuting `b_{s'-k}` past `A_{sk}`** (`bOp_comp_Atil`): the commutator is the
   *scalar* `κ` of FS `eq:StoerrelseC` (`|κ| ≤ 128K₀²𝓁η`, `OpZ_kappa`), so the
   `s`-sum is absorbed by the `θ`-mode window (`OpZ_Atil_sum`) while the scalar
   residual is `O(K₀²𝓁η)`.
3. **The `k`-sum** with the weight `Z²c_k⁻¹Ŵ₁(k)²`: since `k ↦ s-k` is injective and
   lands in `P_H^q` (`PH_subset_PHq_sub`) and `𝒟_q ≥ ‖q‖²/4` there, the pointwise
   bound `c_k⁻¹Ŵ₁(k)² ≤ 2048K₀²K_H⁴a⁶𝒟_{s-k}` (`OpZ_cD_bd`) turns the `k`-sum into
   the reserve `Σ_{q∈P_H^q}𝒟_q b_q†b_q` (`OpZ_reserve`); the lattice weight
   `Σ_k Z²c_k⁻¹Ŵ₁(k)² ≤ 8ρ_zK₀a` is `sum_cD_W1sq_le`.
4. **The arithmetic**: the reserve coefficient is `≤ 𝓁²/8` (`OpZ_RE1`) and the scalar
   remainder is `≤ C·e1A` (`OpZ_Bterm`).  The gap term of the target is nonnegative
   (`gapOpT_qw_nonneg`) and is simply discarded.

All constants are the corpus's coarse ones; `C` and `t₀` depend only on `K₀`, `b₀`.
-/

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

/-- The energy gap `⟨Φ, gapOpT Φ⟩` is nonnegative: `gapOpT` is the sum of the
positive operators `ℓ⁻²n₊` and `ε_T(dℓ)⁻²n₊^H`.  (Local copy of
`Est1.Assembly.gapOpT_qw_nonneg`, kept here so that this module does not depend
on the assembly of `EstQ3oneA`.) -/
theorem gapOpT_qw_nonneg_local {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (hv : FSParamsView E) (Φ : F.H) :
    0 ≤ F.qw Φ (T.gapOpT E) := by
  have heT : 0 ≤ E.eT := eT_nonneg E hv
  have hell : 0 ≤ E.ell := le_of_lt (ell_pos E hv)
  have hd : 0 ≤ E.d := by
    rw [hv.d_eq]; exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
  have h1 : 0 ≤ E.ell ^ (-(2 : ℝ)) := Real.rpow_nonneg hell _
  have h2 : 0 ≤ E.eT * (E.d * E.ell) ^ (-(2 : ℝ)) :=
    mul_nonneg heT (Real.rpow_nonneg (mul_nonneg hd hell) _)
  have hN := T.N_nonneg Φ
  have hNH := T.NH_nonneg Φ
  simp only [FockData.qw, Work.BoseB7A.TildeData.gapOpT, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg h1 hN) (mul_nonneg h2 hNH)

theorem bp_le_half {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (F : FockData Mode) (u v : F.H) :
    F.bp u v ≤ (F.normSq u + F.normSq v) / 2 := by
  have h1 : F.bp u v ≤ |F.bp u v| := le_abs_self _
  have h2 := Work.BoseB7.bp_cauchy_abs F u v
  have h3 : Real.sqrt (F.bp u u) * Real.sqrt (F.bp v v)
      ≤ (F.bp u u + F.bp v v) / 2 := by
    have hx : 0 ≤ F.bp u u := F.bp_nonneg u
    have hy : 0 ≤ F.bp v v := F.bp_nonneg v
    have h4 : 2 * Real.sqrt (F.bp u u) * Real.sqrt (F.bp v v)
        ≤ F.bp u u + F.bp v v := by
      have := sq_nonneg (Real.sqrt (F.bp u u) - Real.sqrt (F.bp v v))
      rw [sub_sq, Real.sq_sqrt hx, Real.sq_sqrt hy] at this
      linarith
    linarith
  calc F.bp u v ≤ |F.bp u v| := h1
    _ ≤ Real.sqrt (F.bp u u) * Real.sqrt (F.bp v v) := h2
    _ ≤ (F.bp u u + F.bp v v) / 2 := h3
    _ = (F.normSq u + F.normSq v) / 2 := rfl

theorem reserve_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode)
    (hAB : ∀ k, |E.B k| ≤ E.A k) (Φ : F.H) :
    0 ≤ F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
  rw [FockData.qw, Work.BoseB7.bp_dNumOpR]
  refine Finset.sum_nonneg fun i _ => ?_
  have hD : 0 ≤ E.D i := by
    have h := FockData.Dcoef_nonneg (hAB i)
    simpa only [Q3Env.D, Dcoef] using h
  exact mul_nonneg hD (Work.BoseB7.bp_bNumOp_nonneg F E.alpha i Φ)

theorem bNumOp_qw_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (F : FockData Mode) (E : Q3Env Mode) (q : Mode) (Φ : F.H) :
    F.bp ((F.bNumOp E.alpha q) Φ) Φ = F.normSq (F.bOp E.alpha q Φ) := by
  rw [FockData.bNumOp, LinearMap.comp_apply, Work.BoseB7.bOpDag_bp]
  rfl

theorem one_sub_alpha_sq_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Q3Env Mode) (q : Mode) (hAB : |E.B q| ≤ E.A q) :
    0 ≤ 1 - E.alpha q ^ 2 := by
  have hA : 0 ≤ E.A q := le_trans (abs_nonneg _) hAB
  rcases lt_or_eq_of_le hA with hApos | hA0
  · rw [Q3Env.alpha, Work.BoseB7.one_sub_alphaCoef_sq hApos hAB]
    have hs : 0 ≤ Submission.BoseGases.bogS (E.A q) (E.B q) :=
      Submission.BoseGases.bogS_nonneg _ _
    have hden : 0 ≤ E.A q + Submission.BoseGases.bogS (E.A q) (E.B q) := by linarith
    positivity
  · have hB : E.B q = 0 := by
      have h : |E.B q| ≤ 0 := hA0.symm ▸ hAB
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hα : E.alpha q = 0 := by
      rw [Q3Env.alpha, hB, ← hA0, Work.BoseB7.alphaCoef]
      simp [Submission.BoseGases.bogAlpha]
    rw [hα]
    norm_num

theorem sum_fL_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) (A : ℝ)
    (hfL0 : ∀ s, 0 ≤ E.fL s) (hfL1 : ∀ s, E.fL s ≤ 1)
    (hcount : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ A) :
    ∑ s ∈ excited Mode, E.fL s ≤ A := by
  have hsplit : ∑ s ∈ excited Mode, E.fL s
      = ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0), E.fL s := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun s _ => by by_cases h : E.fL s = 0 <;> simp [h]
  rw [hsplit]
  calc ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0), E.fL s
      ≤ ∑ _s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0), (1 : ℝ) :=
        Finset.sum_le_sum fun s _ => hfL1 s
    _ = (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) := by simp
    _ ≤ A := hcount

theorem sum_fL_mul_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) (k : Mode) (A : ℝ)
    (hfL0 : ∀ s, 0 ≤ E.fL s) (hfL1 : ∀ s, E.fL s ≤ 1)
    (hcount : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ A)
    (hq : ∀ s, E.fL s ≠ 0 → E.q3Denom s k ≤ 4)
    (hq0 : ∀ s, E.fL s ≠ 0 → 0 ≤ E.q3Denom s k) :
    ∑ s ∈ excited Mode, E.fL s * E.q3Denom s k ≤ 4 * A := by
  have hsplit : ∑ s ∈ excited Mode, E.fL s * E.q3Denom s k
      = ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0), E.fL s * E.q3Denom s k := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun s _ => by by_cases h : E.fL s = 0 <;> simp [h]
  rw [hsplit]
  have hstep : ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0), E.fL s * E.q3Denom s k
      ≤ ∑ _s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0), (4 : ℝ) := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hs' : E.fL s ≠ 0 := (Finset.mem_filter.mp hs).2
    have h1 : E.fL s * E.q3Denom s k ≤ 1 * E.q3Denom s k :=
      mul_le_mul_of_nonneg_right (hfL1 s) (hq0 s hs')
    linarith [hq s hs']
  rw [Finset.sum_const, nsmul_eq_mul] at hstep
  have hcard : 0 ≤ (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) := by positivity
  linarith

theorem sum_cD_W1sq_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) (K₀ : ℝ)
    (hell : 0 < E.ell)
    (hZ : (E.z / E.ell ^ 3) ^ 2 = E.rho / E.ell ^ 3)
    (hpt : ∀ k ∈ F.PHset E,
      (cD E k)⁻¹ * E.W1 k ^ 2 ≤ 8 * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)
    (hsub : ∀ k ∈ F.PHset E, F.PHq E.KH E.aScat k)
    (hsumW : E.ell ^ (-(3 : ℝ)) *
        ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
      ≤ K₀ * E.aScat) :
    ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * E.W1 k ^ 2
      ≤ 8 * E.rho * K₀ * E.aScat := by
  have hsub2 : F.PHset E ⊆ (excited Mode).filter (F.PHq E.KH E.aScat) := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, hsub k hk⟩
  have hmono : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2
      (fun q _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hinv : E.ell ^ 3 * E.ell ^ (-(3 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast E.ell 3, ← Real.rpow_add hell]
    norm_num
  have h3nn : 0 ≤ E.ell ^ 3 := (pow_pos hell 3).le
  have hsum3 : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ E.ell ^ 3 * (K₀ * E.aScat) := by
    have h4 := mul_le_mul_of_nonneg_left hsumW h3nn
    rw [← mul_assoc, hinv, one_mul] at h4
    exact le_trans hmono h4
  have hSnn : 0 ≤ ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hrhonn : 0 ≤ E.rho / E.ell ^ 3 := by
    rw [Q3Env.rho, rhoZ]
    positivity
  calc ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * E.W1 k ^ 2
      = (E.z / E.ell ^ 3) ^ 2 * ∑ k ∈ F.PHset E, (cD E k)⁻¹ * E.W1 k ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (E.z / E.ell ^ 3) ^ 2 * ∑ k ∈ F.PHset E, 8 * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (sq_nonneg _)
    _ = 8 * (E.rho / E.ell ^ 3) * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := by
        have hh : ∑ k ∈ F.PHset E, 8 * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
            = 8 * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [hZ, hh]
        ring
    _ ≤ 8 * (E.rho / E.ell ^ 3) * (E.ell ^ 3 * (K₀ * E.aScat)) :=
        mul_le_mul_of_nonneg_left hsum3 (by positivity)
    _ = 8 * E.rho * K₀ * E.aScat := by
        field_simp

theorem sum_cD_W1sq_subset {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (K₀ : ℝ) (S : Finset Mode)
    (hell : 0 < E.ell)
    (hZ : (E.z / E.ell ^ 3) ^ 2 = E.rho / E.ell ^ 3)
    (hS : S ⊆ F.PHset E)
    (hpt : ∀ k ∈ S,
      (cD E k)⁻¹ * E.W1 k ^ 2 ≤ 8 * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)
    (hsubq : ∀ k ∈ S, F.PHq E.KH E.aScat k)
    (hsumW : E.ell ^ (-(3 : ℝ)) *
        ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
      ≤ K₀ * E.aScat) :
    ∑ k ∈ S, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * E.W1 k ^ 2
      ≤ 8 * E.rho * K₀ * E.aScat := by
  have hsub2 : S ⊆ (excited Mode).filter (F.PHq E.KH E.aScat) := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hS hk)).1, hsubq k hk⟩
  have hmono : ∑ k ∈ S, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2
      (fun q _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hinv : E.ell ^ 3 * E.ell ^ (-(3 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast E.ell 3, ← Real.rpow_add hell]
    norm_num
  have h3nn : 0 ≤ E.ell ^ 3 := (pow_pos hell 3).le
  have hsum3 : ∑ k ∈ S, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ E.ell ^ 3 * (K₀ * E.aScat) := by
    have h4 := mul_le_mul_of_nonneg_left hsumW h3nn
    rw [← mul_assoc, hinv, one_mul] at h4
    exact le_trans hmono h4
  have hSnn : 0 ≤ ∑ k ∈ S, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hrhonn : 0 ≤ E.rho / E.ell ^ 3 := by
    rw [Q3Env.rho, rhoZ]
    positivity
  calc ∑ k ∈ S, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * E.W1 k ^ 2
      = (E.z / E.ell ^ 3) ^ 2 * ∑ k ∈ S, (cD E k)⁻¹ * E.W1 k ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (E.z / E.ell ^ 3) ^ 2 * ∑ k ∈ S, 8 * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (sq_nonneg _)
    _ = 8 * (E.rho / E.ell ^ 3) * ∑ k ∈ S, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := by
        have hh : ∑ k ∈ S, 8 * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
            = 8 * ∑ k ∈ S, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [hZ, hh]
        ring
    _ ≤ 8 * (E.rho / E.ell ^ 3) * (E.ell ^ 3 * (K₀ * E.aScat)) :=
        mul_le_mul_of_nonneg_left hsum3 (by positivity)
    _ = 8 * E.rho * K₀ * E.aScat := by
        field_simp


end Est1

end Work.BoseC3QAll
