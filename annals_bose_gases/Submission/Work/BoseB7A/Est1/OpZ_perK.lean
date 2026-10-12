import Mathlib.Tactic.Module
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.Est1.T2algebra
import Submission.Work.BoseB7A.Est1.estT2sum_defs
import Submission.Work.BoseB7A.NWindow_bp_N_le
import Submission.Work.BoseB7A.NWindow_shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Est1.OpZ_perK` — the per-`k` bound on `T₂,op`

The normal-ordered half `T2OpF` of `‖Y_kΦ‖²/Z²` (FS `eq:T2opprime`), bounded for a
*single* mode `k` by the two quantities which the `k`-sum of `estT2sum_opZ` then
absorbs:

  `T2OpF F T E k Φ ≤ Ŵ₁(k)²·( 32(𝓜+1+K₀(K_ℓK_L)³)·Σ_{s'}f_L(s')q3Denom(s',k)‖b_{s'-k}Φ‖²
                    + 32(K₀(K_ℓK_L)³)²·(128K₀²𝓁η)²·‖Φ‖² )`.

The statement is stated **only** through the four interface hypotheses in which the
`Q3Kernel` fields enter this estimate:

* `hsumw` — the total weight `Σ_{s∈excited}f_L(s)q3Denom(s,k) ≤ 4K₀(K_ℓK_L)³`;
* `hκ` — the scalar commutator `[Ã_{sk}, b_{s'-k}] =
  α_{s'-k}χ̂(-(s'-k)) - α_kα_{s-k}χ̂(s'-k)` is `O(K₀²𝓁η)`
  (`Est1.kscal`, from `Est1.Atil_comp_bOp`);
* `hAtil` — the window estimate `Σ_s f_L(s)q3Denom(s,k)‖Ã_{sk}v‖² ≤ 16(𝓜+1+…)‖v‖²`
  for `v` in `NWindow (𝓜+1)` (`Est1.OpZ_Atil_sum`);
* `hΦ` — `Φ ∈ NWindow 𝓜`, used only through `NWindow_shift` to put the `b_{s'-k}Φ`
  of `hAtil` inside the window.

## The proof

Write `γ_{sk} = gA E s k = f_L(s)Ŵ₁(k)q3Denom(s,k)` (so `γ_{sk}γ_{s'k} =
Ŵ₁(k)²·w_s w_{s'}` with `w_s = f_L(s)q3Denom(s,k) ≥ 0`) and `Ã_{sk} = Atil F T E s k`.

1. **Cauchy–Schwarz (AM–GM)** in the Fock form (`OpZ_sum_bp_le_normSq`):
   the symmetric double sum `Σ_{s,s'}γ_sγ_{s'}⟨u_{ss'},v_{ss'}⟩` is at most
   `Σ_{s,s'}γ_sγ_{s'}‖u_{ss'}‖²`, because the two halves of
   `2⟨u,v⟩ ≤ ‖u‖²+‖v‖²` are interchanged by `(s,s') ↦ (s',s)`
   (`OpZ_dsum_symm`).
2. **Commute `b_{s'-k}` past `Ã_{sk}`** (`OpZ_kscal_comm`, FS `eq:StoerrelseC`):
   `b_{s'-k}Ã_{sk}Φ = Ã_{sk}(b_{s'-k}Φ) - κ_{ss'}Φ`, so
   `‖b_{s'-k}Ã_{sk}Φ‖² ≤ 2‖Ã_{sk}(b_{s'-k}Φ)‖² + 2κ_{ss'}²‖Φ‖²`.
3. **The window part**: `‖Φ‖²`-free, `Σ_s w_s‖Ã_{sk}v‖² ≤ 16(𝓜+1+…)‖v‖²` with
   `v = b_{s'-k}Φ ∈ NWindow (𝓜+1)` (`NWindow_shift`); factoring `Ŵ₁(k)²` out of the
   double and re-summing over `s` for each `s'` (`Finset.sum_comm`) gives
   `32Ŵ₁(k)²(𝓜+1+…)Σ_{s'}w_{s'}‖b_{s'-k}Φ‖²`.
4. **The `κ²` part**: `γ_sγ_{s'}κ_{ss'}² ≤ γ_sγ_{s'}κ₀²` (`hκ`, with the
   `f_L(s) = 0` case trivially zero because then `γ_sγ_{s'} = 0`), and
   `Σ_{s,s'}γ_sγ_{s'} = Ŵ₁(k)²(Σ_s w_s)² ≤ Ŵ₁(k)²(4K₀(K_ℓK_L)³)²` by `hsumw`.

Both coefficients are exactly the ones in the target (the `32 = 2·16` is the factor
`2` of the norm bound and the `16` of `hAtil`), and no count of `P_H` is used.
-/

noncomputable section
open scoped BigOperators
namespace Work.BoseB7A.Est1
open Work.BoseB7
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

lemma OpZ_bp_half_le (F : FockData Mode) (u v : F.H) :
    F.bp u v ≤ (F.normSq u + F.normSq v) / 2 := by
  have h := Work.BoseB7.bp_cauchy F (by norm_num : (0 : ℝ) < 1) u v
  rw [one_mul, inv_one] at h
  rw [FockData.normSq, FockData.normSq]
  linarith

lemma OpZ_normSq_add_le (F : FockData Mode) (u v : F.H) :
    F.normSq (u + v) ≤ 2 * F.normSq u + 2 * F.normSq v := by
  have h1 : F.normSq (u + v) = F.normSq u + 2 * F.bp u v + F.normSq v := by
    simp only [FockData.normSq, map_add, LinearMap.add_apply, F.bp_symm]
    ring
  have h2 := OpZ_bp_half_le F u v
  rw [h1]
  linarith

lemma OpZ_normSq_neg (F : FockData Mode) (u : F.H) : F.normSq (-u) = F.normSq u := by
  simp only [FockData.normSq, map_neg, LinearMap.neg_apply]
  ring

lemma OpZ_normSq_sub_le (F : FockData Mode) (u v : F.H) :
    F.normSq (u - v) ≤ 2 * F.normSq u + 2 * F.normSq v := by
  rw [sub_eq_add_neg]
  calc F.normSq (u + -v) ≤ 2 * F.normSq u + 2 * F.normSq (-v) := OpZ_normSq_add_le F u (-v)
    _ = 2 * F.normSq u + 2 * F.normSq v := by rw [OpZ_normSq_neg]

lemma OpZ_normSq_smul (F : FockData Mode) (c : ℝ) (u : F.H) :
    F.normSq (c • u) = c ^ 2 * F.normSq u := by
  simp only [FockData.normSq, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

lemma OpZ_dsum_symm {X : Finset Mode} {M : Mode → Mode → ℝ} (hMs : ∀ a b, M a b = M b a)
    (g : Mode → Mode → ℝ) :
    (∑ a ∈ X, ∑ b ∈ X, M a b * g b a) = ∑ a ∈ X, ∑ b ∈ X, M a b * g a b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hMs b a]

lemma OpZ_sum_bp_le_normSq (F : FockData Mode) {X : Finset Mode} {M : Mode → Mode → ℝ}
    (hM0 : ∀ a b, 0 ≤ M a b) (hMs : ∀ a b, M a b = M b a)
    (u v : Mode → Mode → F.H) (huv : ∀ a b, v a b = u b a) :
    (∑ a ∈ X, ∑ b ∈ X, M a b * F.bp (u a b) (v a b))
      ≤ ∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (u a b) := by
  have hswap : (∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (v a b))
      = ∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (u a b) := by
    have h1 : (∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (v a b))
        = ∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (u b a) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [huv a b]
    rw [h1]
    exact OpZ_dsum_symm hMs (fun a b => F.normSq (u a b))
  have hpt : ∀ a ∈ X, ∀ b ∈ X, M a b * F.bp (u a b) (v a b)
      ≤ M a b * ((F.normSq (u a b) + F.normSq (v a b)) / 2) :=
    fun a _ b _ => mul_le_mul_of_nonneg_left (OpZ_bp_half_le F (u a b) (v a b)) (hM0 a b)
  have hmid : (∑ a ∈ X, ∑ b ∈ X, M a b * ((F.normSq (u a b) + F.normSq (v a b)) / 2))
      = (1/2) * (∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (u a b))
        + (1/2) * (∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (v a b)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => by ring
  calc (∑ a ∈ X, ∑ b ∈ X, M a b * F.bp (u a b) (v a b))
      ≤ ∑ a ∈ X, ∑ b ∈ X, M a b * ((F.normSq (u a b) + F.normSq (v a b)) / 2) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hpt a ha b hb
    _ = (1/2) * (∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (u a b))
        + (1/2) * (∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (v a b)) := hmid
    _ = ∑ a ∈ X, ∑ b ∈ X, M a b * F.normSq (u a b) := by rw [hswap]; ring

def kscal {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) : ℝ :=
  E.alpha q * T.ccrX s (-q) - bA E s k * T.ccrX (-s) q

lemma OpZ_kscal_comm {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode) (s k q : Mode) (y : F.H) :
    F.bOp E.alpha q (Atil F T E s k y)
      = Atil F T E s k (F.bOp E.alpha q y) - (kscal T E s k q) • y := by
  have h2 : F.bOp E.alpha q ∘ₗ Atil F T E s k
      = Atil F T E s k ∘ₗ F.bOp E.alpha q - (kscal T E s k q) • (1 : F.H →ₗ[ℝ] F.H) := by
    rw [Atil_comp_bOp, kscal]
    module
  have h3 := LinearMap.congr_fun h2 y
  simpa using h3

lemma OpZ_normSq_bOp_Atil_le {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode)
    (s k q : Mode) (Φ : F.H) :
    F.normSq (F.bOp E.alpha q (Atil F T E s k Φ))
      ≤ 2 * F.normSq (Atil F T E s k (F.bOp E.alpha q Φ))
        + 2 * (kscal T E s k q) ^ 2 * F.normSq Φ := by
  rw [OpZ_kscal_comm]
  calc F.normSq (Atil F T E s k (F.bOp E.alpha q Φ) - kscal T E s k q • Φ)
      ≤ 2 * F.normSq (Atil F T E s k (F.bOp E.alpha q Φ)) + 2 * F.normSq (kscal T E s k q • Φ) :=
        OpZ_normSq_sub_le F _ _
    _ = 2 * F.normSq (Atil F T E s k (F.bOp E.alpha q Φ)) + 2 * ((kscal T E s k q) ^ 2 * F.normSq Φ) := by
        rw [OpZ_normSq_smul]
    _ = 2 * F.normSq (Atil F T E s k (F.bOp E.alpha q Φ)) + 2 * (kscal T E s k q) ^ 2 * F.normSq Φ := by ring

theorem OpZ_perK {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) {K₀ : ℝ} {k : Mode} {Φ : F.H}
    (hΦ : T.NWindow E.bigM Φ) (hMnn : 0 ≤ E.bigM)
    (hfL0 : ∀ s, 0 ≤ E.fL s)
    (hq3nn : ∀ s, 0 ≤ E.q3Denom s k)
    (hsumw : ∑ s ∈ Work.BoseB7.excited Mode, E.fL s * E.q3Denom s k
      ≤ 4 * (K₀ * (E.Kl * E.KL) ^ 3))
    (hκ : ∀ s s', E.fL s ≠ 0 → E.fL s' ≠ 0 →
      |E.alpha (s' - k) * T.ccrX s (-(s' - k)) - Work.BoseB7A.Est1.bA E s k * T.ccrX (-s) (s' - k)|
        ≤ 128 * K₀ ^ 2 * E.lille * Work.BoseB7A.eta E)
    (hAtil : ∀ v : F.H, T.NWindow (E.bigM + 1) v →
      ∑ s ∈ Work.BoseB7.excited Mode, E.fL s * E.q3Denom s k * F.normSq (Work.BoseB7A.Est1.Atil F T E s k v)
        ≤ 16 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3) * F.normSq v) :
    Work.BoseB7A.Est1.T2OpF F T E k Φ ≤ E.W1 k ^ 2 *
      (32 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3) *
          (∑ s' ∈ Work.BoseB7.excited Mode,
            E.fL s' * E.q3Denom s' k * F.normSq (F.bOp E.alpha (s' - k) Φ))
        + 32 * (K₀ * (E.Kl * E.KL) ^ 3) ^ 2
            * (128 * K₀ ^ 2 * E.lille * Work.BoseB7A.eta E) ^ 2 * F.normSq Φ) := by
  have hw0 : ∀ s : Mode, 0 ≤ E.fL s * E.q3Denom s k := fun s => mul_nonneg (hfL0 s) (hq3nn s)
  have hM0 : ∀ a b : Mode, 0 ≤ gA E a k * gA E b k := by
    intro a b
    have h1 : 0 ≤ (E.W1 k) ^ 2 * ((E.fL a * E.q3Denom a k) * (E.fL b * E.q3Denom b k)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (hw0 a) (hw0 b))
    refine le_of_le_of_eq h1 ?_
    rw [gA, gA]; ring
  have hMs : ∀ a b : Mode, gA E a k * gA E b k = gA E b k * gA E a k :=
    fun a b => mul_comm _ _
  have hNW : ∀ b : Mode, T.NWindow (E.bigM + 1) (F.bOp E.alpha (b - k) Φ) :=
    fun b => (NWindow_shift F T E hMnn hΦ 0 (b - k)).2.2.2.2.2.2.1
  have hnorm : ∀ a b : Mode, F.normSq (F.bOp E.alpha (b - k) (Atil F T E a k Φ))
      ≤ 2 * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ))
        + 2 * (kscal T E a k (b - k)) ^ 2 * F.normSq Φ :=
    fun a b => OpZ_normSq_bOp_Atil_le T E a k (b - k) Φ
  have hkpt : ∀ a b : Mode, (gA E a k * gA E b k) * (kscal T E a k (b - k)) ^ 2
      ≤ (gA E a k * gA E b k) * (128 * K₀ ^ 2 * E.lille * eta E) ^ 2 := by
    intro a b
    by_cases h : gA E a k * gA E b k = 0
    · rw [h, zero_mul, zero_mul]
    · have hfa : E.fL a ≠ 0 := fun h0 => h (by rw [gA, gA, h0]; ring)
      have hfb : E.fL b ≠ 0 := fun h0 => h (by rw [gA, gA, h0]; ring)
      have hkb : |kscal T E a k (b - k)| ≤ 128 * K₀ ^ 2 * E.lille * eta E := by
        rw [kscal]
        exact hκ a b hfa hfb
      have hk0 : 0 ≤ 128 * K₀ ^ 2 * E.lille * eta E := le_trans (abs_nonneg _) hkb
      refine mul_le_mul_of_nonneg_left ?_ (hM0 a b)
      refine sq_le_sq.mpr ?_
      rwa [abs_of_nonneg hk0]
  have hI : T2OpF F T E k Φ ≤
      ∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
        (gA E a k * gA E b k) * F.normSq (F.bOp E.alpha (b - k) (Atil F T E a k Φ)) := by
    rw [T2OpF]
    exact OpZ_sum_bp_le_normSq F hM0 hMs
      (fun a b => F.bOp E.alpha (b - k) (Atil F T E a k Φ))
      (fun a b => F.bOp E.alpha (a - k) (Atil F T E b k Φ)) (fun a b => rfl)
  have hII : (∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
        (gA E a k * gA E b k) * F.normSq (F.bOp E.alpha (b - k) (Atil F T E a k Φ)))
      ≤ 2 * (∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
            (gA E a k * gA E b k) * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ)))
        + 2 * (∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
            (gA E a k * gA E b k) * ((kscal T E a k (b - k)) ^ 2 * F.normSq Φ)) := by
    have h1 : (∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
          (gA E a k * gA E b k) * F.normSq (F.bOp E.alpha (b - k) (Atil F T E a k Φ)))
        ≤ ∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
          (gA E a k * gA E b k) * (2 * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ))
            + 2 * (kscal T E a k (b - k)) ^ 2 * F.normSq Φ) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hnorm a b) (hM0 a b)
    have h2 : (∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
          (gA E a k * gA E b k) * (2 * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ))
            + 2 * (kscal T E a k (b - k)) ^ 2 * F.normSq Φ))
        = ∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
            (2 * ((gA E a k * gA E b k) * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ)))
              + 2 * ((gA E a k * gA E b k) * ((kscal T E a k (b - k)) ^ 2 * F.normSq Φ))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    refine le_trans h1 ?_
    rw [h2]
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
    exact le_refl _
  have hIII : (∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
        (gA E a k * gA E b k) * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ)))
      ≤ (E.W1 k) ^ 2 * (16 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
          * (∑ b ∈ excited Mode, E.fL b * E.q3Denom b k * F.normSq (F.bOp E.alpha (b - k) Φ))) := by
    have hfac : ∀ a b : Mode,
        (gA E a k * gA E b k) * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ))
        = (E.W1 k) ^ 2 * (((E.fL a * E.q3Denom a k) * (E.fL b * E.q3Denom b k))
            * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ))) := by
      intro a b; rw [gA, gA]; ring
    have hEq : (∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
          (gA E a k * gA E b k) * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ)))
        = (E.W1 k) ^ 2 * (∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
          ((E.fL a * E.q3Denom a k) * (E.fL b * E.q3Denom b k))
            * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ))) := by
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hfac a b))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    rw [hEq]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [Finset.sum_comm]
    have hper : ∀ b : Mode,
        (∑ a ∈ excited Mode, ((E.fL a * E.q3Denom a k) * (E.fL b * E.q3Denom b k))
            * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ)))
        ≤ (E.fL b * E.q3Denom b k) * (16 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
            * F.normSq (F.bOp E.alpha (b - k) Φ)) := by
      intro b
      have hA : (∑ a ∈ excited Mode, ((E.fL a * E.q3Denom a k) * (E.fL b * E.q3Denom b k))
            * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ)))
          = (E.fL b * E.q3Denom b k) * (∑ a ∈ excited Mode,
              E.fL a * E.q3Denom a k * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by ring
      rw [hA]
      exact mul_le_mul_of_nonneg_left (hAtil _ (hNW b)) (hw0 b)
    calc (∑ b ∈ excited Mode, ∑ a ∈ excited Mode,
            ((E.fL a * E.q3Denom a k) * (E.fL b * E.q3Denom b k))
              * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ)))
        ≤ ∑ b ∈ excited Mode, (E.fL b * E.q3Denom b k) * (16 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
              * F.normSq (F.bOp E.alpha (b - k) Φ)) :=
          Finset.sum_le_sum fun b _ => hper b
      _ = 16 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
            * (∑ b ∈ excited Mode, E.fL b * E.q3Denom b k * F.normSq (F.bOp E.alpha (b - k) Φ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring
  have hIV : (∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
        (gA E a k * gA E b k) * ((kscal T E a k (b - k)) ^ 2 * F.normSq Φ))
      ≤ (E.W1 k) ^ 2 * (16 * (K₀ * (E.Kl * E.KL) ^ 3) ^ 2
          * (128 * K₀ ^ 2 * E.lille * eta E) ^ 2 * F.normSq Φ) := by
    have hprod : (∑ a ∈ excited Mode, ∑ b ∈ excited Mode, gA E a k * gA E b k)
        = (∑ a ∈ excited Mode, gA E a k) * (∑ b ∈ excited Mode, gA E b k) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    have hsumgA : (∑ a ∈ excited Mode, gA E a k)
        = (E.W1 k) * (∑ a ∈ excited Mode, E.fL a * E.q3Denom a k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [gA]; ring
    have hsq : (∑ a ∈ excited Mode, E.fL a * E.q3Denom a k) ^ 2
        ≤ (4 * (K₀ * (E.Kl * E.KL) ^ 3)) ^ 2 := by
      have h0 : 0 ≤ ∑ a ∈ excited Mode, E.fL a * E.q3Denom a k := Finset.sum_nonneg fun a _ => hw0 a
      have h1 : 0 ≤ 4 * (K₀ * (E.Kl * E.KL) ^ 3) := le_trans h0 hsumw
      rw [sq_le_sq, abs_of_nonneg h0, abs_of_nonneg h1]
      exact hsumw
    calc (∑ a ∈ excited Mode, ∑ b ∈ excited Mode, (gA E a k * gA E b k) * ((kscal T E a k (b - k)) ^ 2 * F.normSq Φ))
        ≤ ∑ a ∈ excited Mode, ∑ b ∈ excited Mode,
            (gA E a k * gA E b k) * ((128 * K₀ ^ 2 * E.lille * eta E) ^ 2 * F.normSq Φ) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
            calc (gA E a k * gA E b k) * ((kscal T E a k (b - k)) ^ 2 * F.normSq Φ)
                = ((gA E a k * gA E b k) * (kscal T E a k (b - k)) ^ 2) * F.normSq Φ := by ring
              _ ≤ ((gA E a k * gA E b k) * (128 * K₀ ^ 2 * E.lille * eta E) ^ 2) * F.normSq Φ :=
                  mul_le_mul_of_nonneg_right (hkpt a b) (F.normSq_nonneg Φ)
              _ = (gA E a k * gA E b k) * ((128 * K₀ ^ 2 * E.lille * eta E) ^ 2 * F.normSq Φ) := by ring
      _ = (∑ a ∈ excited Mode, ∑ b ∈ excited Mode, gA E a k * gA E b k)
            * ((128 * K₀ ^ 2 * E.lille * eta E) ^ 2 * F.normSq Φ) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
      _ = ((E.W1 k) ^ 2 * (∑ a ∈ excited Mode, E.fL a * E.q3Denom a k) ^ 2)
            * ((128 * K₀ ^ 2 * E.lille * eta E) ^ 2 * F.normSq Φ) := by
          rw [hprod, hsumgA]; ring
      _ ≤ ((E.W1 k) ^ 2 * (4 * (K₀ * (E.Kl * E.KL) ^ 3)) ^ 2)
            * ((128 * K₀ ^ 2 * E.lille * eta E) ^ 2 * F.normSq Φ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))
            (mul_nonneg (sq_nonneg _) (F.normSq_nonneg Φ))
      _ = (E.W1 k) ^ 2 * (16 * (K₀ * (E.Kl * E.KL) ^ 3) ^ 2
            * (128 * K₀ ^ 2 * E.lille * eta E) ^ 2 * F.normSq Φ) := by ring
  refine le_trans hI (le_trans hII ?_)
  calc 2 * (∑ a ∈ excited Mode, ∑ b ∈ excited Mode, (gA E a k * gA E b k) * F.normSq (Atil F T E a k (F.bOp E.alpha (b - k) Φ)))
        + 2 * (∑ a ∈ excited Mode, ∑ b ∈ excited Mode, (gA E a k * gA E b k) * ((kscal T E a k (b - k)) ^ 2 * F.normSq Φ))
      ≤ 2 * ((E.W1 k) ^ 2 * (16 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
            * (∑ b ∈ excited Mode, E.fL b * E.q3Denom b k * F.normSq (F.bOp E.alpha (b - k) Φ))))
        + 2 * ((E.W1 k) ^ 2 * (16 * (K₀ * (E.Kl * E.KL) ^ 3) ^ 2
            * (128 * K₀ ^ 2 * E.lille * eta E) ^ 2 * F.normSq Φ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hIII (by norm_num))
          (mul_le_mul_of_nonneg_left hIV (by norm_num))
    _ = (E.W1 k) ^ 2 * (32 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3)
            * (∑ s' ∈ Work.BoseB7.excited Mode,
              E.fL s' * E.q3Denom s' k * F.normSq (F.bOp E.alpha (s' - k) Φ))
          + 32 * (K₀ * (E.Kl * E.KL) ^ 3) ^ 2
              * (128 * K₀ ^ 2 * E.lille * Work.BoseB7A.eta E) ^ 2 * F.normSq Φ) := by ring

end Work.BoseB7A.Est1
