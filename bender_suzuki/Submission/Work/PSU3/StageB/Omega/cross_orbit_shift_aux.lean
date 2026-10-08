/-
# `Work.PSU3.StageB.Omega.cross_orbit_shift_aux` — infrastructure for Peterfalvi II Ch. VII §2 (20)

Auxiliary lemmas for the proof of the cross-orbit translation identity `Omega.cross_orbit_shift`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.Omega.beta_pow_setup
import Submission.Work.PSU3.StageB.Omega.beta_pow_m_eq_one
import Submission.Work.PSU3.StageB.Omega.orderOf_beta_eq
import Submission.Work.PSU3.StageB.Omega.fcan_zU_eq_vSeq
import Submission.Work.PSU3.StageB.Omega.fcan_step10
import Submission.Work.PSU3.StageB.Omega.cross_orbit_datum
import Submission.Work.PSU3.StageB.Omega.alpha_eq_of_two_orbits
import Submission.Work.PSU3.StageB.Omega.count_le
import Submission.Work.PSU3.StageB.Omega.count_self_eq
import Submission.Work.PSU3.StageB.Omega.orbE_card
import Submission.Work.PSU3.StageB.Omega.exists_zcQF_eq_of_mem_Q0
import Submission.Work.PSU3.StageB.Omega.exists_coset_zeta
import Submission.Work.PSU3.StageB.Omega.uSeq_div
import Submission.Work.PSU3.StageB.Omega.coset_sep
import Submission.Work.PSU3.StageB.Omega.fcan_eq_qconj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## `κ`-values of `Ksub`-elements; their conjugation action on `Q₀` -/

/-- `κ k` as an element of `FX n`, for `k ∈ Ksub H t`. -/
noncomputable def kapFX (fr : CoarseFrame H Q t n) {k : fr.KW} (hk : (k : G) ∈ Ksub H t) :
    ↥(FX n) := ⟨fr.κ k, (fr.mem_K_iff k).mp hk⟩

lemma fval_kapFX (fr : CoarseFrame H Q t n) {k : fr.KW} (hk : (k : G) ∈ Ksub H t) :
    fval (kapFX fr hk) = (fr.κ k : E n) := rfl

lemma nmF_kapFX (fr : CoarseFrame H Q t n) {k : fr.KW} (hk : (k : G) ∈ Ksub H t) :
    fval (nmF fr (kapFX fr hk)) = (fr.nm (fr.κ k) : E n) := rfl

/-- `k⁻¹ (zc y) k = zc (nm (κ k) y)` — the conjugation action of a `Ksub`-element. -/
lemma conj_kapFX (fr : CoarseFrame H Q t n) {k : fr.KW} (hk : (k : G) ∈ Ksub H t)
    (y : E n) (hy : σE y = y) :
    (k : G)⁻¹ * fr.zc y * (k : G) = fr.zc (fval (nmF fr (kapFX fr hk)) * y) :=
  fr.act_zc_K k hk y hy

/-- `kact k (zcQF u)` in `G`. -/
lemma kact_kapFX_coe (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {k : fr.KW}
    (hk : (k : G) ∈ Ksub H t) (u : ↥(FX n)) :
    ((kact hS fr k (zcQF fr u) : ↥Q) : G) =
      fr.zc (fval (nmF fr (kapFX fr hk)) * fval u) := by
  rw [kact_coe, zcQF_coe]
  exact fr.act_zc_K k hk (fval u) u.2

/-- `kact k⁻¹ (zcQF u)` in `G`. -/
lemma kact_kapFX_inv_coe (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {k : fr.KW}
    (hk : (k : G) ∈ Ksub H t) (u : ↥(FX n)) :
    ((kact hS fr k⁻¹ (zcQF fr u) : ↥Q) : G) =
      fr.zc ((fval (nmF fr (kapFX fr hk)))⁻¹ * fval u) := by
  have hk' : (((k⁻¹ : fr.KW)) : G) ∈ Ksub H t := (Ksub H t).inv_mem hk
  have h := fr.act_zc_K k⁻¹ hk' (fval u) u.2
  rw [Subgroup.coe_inv, inv_inv] at h
  have hnm : (((fr.nm (fr.κ (k⁻¹)) : (E n)ˣ)) : E n) =
      (fval (nmF fr (kapFX fr hk)))⁻¹ := by
    rw [nmF_kapFX, map_inv, map_inv, Units.val_inv_eq_inv_val]
  rw [hnm] at h
  rw [kact_coe, zcQF_coe, Subgroup.coe_inv, inv_inv]
  exact h

/-- `kact (dSeq lam i)⁻¹ (zcQF u)` in `G`. -/
lemma kact_dSeq_inv_coe (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (lam : ℕ → ↥(FX n))
    (i : ℕ) (u : ↥(FX n)) :
    ((kact hS fr ((dSeq hS fr lam i)⁻¹) (zcQF fr u) : ↥Q) : G) =
      fr.zc ((fval (lam i))⁻¹ * fval u) := by
  have hfix : σE ((fval (lam i))⁻¹ * fval u) = (fval (lam i))⁻¹ * fval u := by
    rw [map_mul, map_inv₀, (lam i).2, u.2]
  have h := dSeq_act hS fr lam i ((fval (lam i))⁻¹ * fval u) hfix
  have hne : fval (lam i) ≠ 0 := Units.ne_zero (lam i).1
  have h2 : fval (lam i) * ((fval (lam i))⁻¹ * fval u) = fval u := by
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [h2] at h
  rw [kact_coe, zcQF_coe, Subgroup.coe_inv, inv_inv]
  have h4 := congrArg
    (fun w : G => (dSeq hS fr lam i : G) * w * ((dSeq hS fr lam i : G))⁻¹) h
  rw [show (dSeq hS fr lam i : G) *
      ((dSeq hS fr lam i : G)⁻¹ * fr.zc ((fval (lam i))⁻¹ * fval u) *
        (dSeq hS fr lam i : G)) * ((dSeq hS fr lam i : G))⁻¹
      = fr.zc ((fval (lam i))⁻¹ * fval u) from by group] at h4
  exact h4.symm

/-! ## `β^i ≠ 1` below `orderOf ζ` -/

/-- `bS β i ≠ 0` for `1 ≤ i < orderOf fr.ζ`, i.e. `β^i ≠ 1`. -/
theorem bS_ne_zero_of_lt_orderOf (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {β : E n} (hβ : β ≠ 0) (hβα : β + β⁻¹ = fval α) :
    ∀ i, 1 ≤ i → i < orderOf fr.ζ → bS β i ≠ 0 := by
  intro i hi hlt
  have hord : orderOf β = orderOf fr.ζ := orderOf_beta_eq hS fr hω hωf hβ hβα
  rw [bS_ne_zero_iff β hβ i]
  intro hb
  have hdvd : orderOf β ∣ i := orderOf_dvd_iff_pow_eq_one.mpr hb
  have hbm : β ^ orderOf fr.ζ = 1 := beta_pow_m_eq_one hS fr hω hωf hβ hβα
  have hdvd0 : orderOf β ∣ orderOf fr.ζ := orderOf_dvd_iff_pow_eq_one.mpr hbm
  have hpos : 0 < orderOf β := Nat.pos_of_dvd_of_pos hdvd0 (orderOf_pos fr.ζ)
  have hle : orderOf β ≤ i := Nat.le_of_dvd (by omega) hdvd
  have : i < orderOf β := by rw [hord]; exact hlt
  omega

/-! ## `t`-conjugation on `KW` -/

lemma tconjKW_exists (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) :
    ∃ e : fr.KW, (e : G) = t * (d : G) * t := by
  obtain ⟨k, hkK, j, hdj⟩ := fr.KW_gen d
  refine ⟨fr.ζ ^ j * k⁻¹, ?_⟩
  have htt : t * t = 1 := mul_self_eq_one hS.split
  have htζ : ∀ m : ℕ, t * (fr.ζ : G) ^ m * t = (fr.ζ : G) ^ m := by
    intro m
    have h1 : (MulAut.conj t) (fr.ζ : G) = (fr.ζ : G) := by
      rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_left htt]
      exact t_zeta_t hS.split fr
    conv_lhs => rw [show t * (fr.ζ : G) ^ m * t = (MulAut.conj t) ((fr.ζ : G) ^ m) from by
      rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_left htt]]
    rw [map_pow, h1]
  have hkt : t * (k : G) * t = (k : G)⁻¹ := tconj_eq_inv hS.split fr hkK
  have hcoe : ((fr.ζ ^ j * k⁻¹ : fr.KW) : G) = (fr.ζ : G) ^ j * (k : G)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
  have hd : (d : G) = (k : G) * (fr.ζ : G) ^ j := by rw [hdj]; rfl
  rw [hcoe, hd]
  calc (fr.ζ : G) ^ j * (k : G)⁻¹
      = (k : G)⁻¹ * (fr.ζ : G) ^ j := KW_comm fr (fr.ζ ^ j) k⁻¹
    _ = (t * (k : G) * t) * (t * (fr.ζ : G) ^ j * t) := by rw [hkt, htζ j]
    _ = t * ((k : G) * (fr.ζ : G) ^ j) * t := by
        have h : t * (k : G) * t * (t * (fr.ζ : G) ^ j * t)
            = t * (k : G) * (t * t) * (fr.ζ : G) ^ j * t := by group
        rw [h, htt, mul_one]
        simp only [mul_assoc]

/-- The `t`-conjugate of `d ∈ KW`, as an element of `KW`. -/
noncomputable def tconjKW (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) : fr.KW :=
  Classical.choose (tconjKW_exists hS fr d)

lemma tconjKW_coe (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) :
    (tconjKW hS fr d : G) = t * (d : G) * t :=
  Classical.choose_spec (tconjKW_exists hS fr d)

/-! ## The `ζ`-exponent of `κ d` on `KW` -/

/-- `FX n ⊓ ⟨κ ζ⟩ = ⊥`: an element of `F*` which is a power of `κ ζ` is trivial. -/
lemma fx_inter_zpowers_zeta (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) :
    FX n ⊓ Subgroup.zpowers (fr.κ fr.ζ) = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  set N : Subgroup (E n)ˣ :=
    { carrier := {v | ((v : (E n)ˣ) : E n) * σE ((v : (E n)ˣ) : E n) = 1}
      mul_mem' := by
        intro a b ha hb
        have ha' : ((a : (E n)ˣ) : E n) * σE ((a : (E n)ˣ) : E n) = 1 := ha
        have hb' : ((b : (E n)ˣ) : E n) * σE ((b : (E n)ˣ) : E n) = 1 := hb
        show (((a * b : (E n)ˣ) : E n)) * σE (((a * b : (E n)ˣ) : E n)) = 1
        have h : (((a * b : (E n)ˣ) : E n)) * σE (((a * b : (E n)ˣ) : E n))
            = (((a : (E n)ˣ) : E n) * σE (((a : (E n)ˣ) : E n)))
              * (((b : (E n)ˣ) : E n) * σE (((b : (E n)ˣ) : E n))) := by
          rw [Units.val_mul, map_mul]; ring
        rw [h, ha', hb', one_mul]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        have ha' : ((a : (E n)ˣ) : E n) * σE ((a : (E n)ˣ) : E n) = 1 := ha
        show (((a⁻¹ : (E n)ˣ) : E n)) * σE (((a⁻¹ : (E n)ˣ) : E n)) = 1
        have h : (((a⁻¹ : (E n)ˣ) : E n)) * σE (((a⁻¹ : (E n)ˣ) : E n))
            = ((((a : (E n)ˣ) : E n) * σE (((a : (E n)ˣ) : E n))))⁻¹ := by
          rw [Units.val_inv_eq_inv_val, σE_inv, ← mul_inv]
        rw [h, ha', inv_one] }
  have hgen : fr.κ fr.ζ ∈ N := fr.ζ_norm
  have hmem : u ∈ N := Subgroup.zpowers_le.mpr hgen hu.2
  have h1 : ((u : (E n)ˣ) : E n) * ((u : (E n)ˣ) : E n) = 1 := by
    have h2 : ((u : (E n)ˣ) : E n) * σE ((u : (E n)ˣ) : E n) = 1 := hmem
    rw [show σE (((u : (E n)ˣ) : E n)) = ((u : (E n)ˣ) : E n) from hu.1] at h2
    exact h2
  exact Units.ext (orbE_eq_one_of_mul_self_eq_one h1)

/-- **The `ζ`-decomposition of `κ d`.**  For `d ∈ KW` there are `j < orderOf fr.ζ` and
`f ∈ F*` with `κ d = ζ^j · f`. -/
lemma exists_kapFX_zeta_coset (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) :
    ∃ j : ℕ, j < orderOf fr.ζ ∧ ∃ f : ↥(FX n),
      (fr.κ d : E n) = (fr.κ fr.ζ : E n) ^ j * fval f := by
  obtain ⟨k, hkK, i, hdi⟩ := fr.KW_gen d
  refine ⟨i % orderOf fr.ζ, Nat.mod_lt _ (orderOf_pos fr.ζ), kapFX fr hkK, ?_⟩
  have hκ : (fr.κ d : E n) = (fr.κ k : E n) * (fr.κ fr.ζ : E n) ^ i := by
    have h1 : fr.κ d = fr.κ k * fr.κ (fr.ζ ^ i) := by rw [hdi, map_mul]
    have h2 : fr.κ (fr.ζ ^ i) = (fr.κ fr.ζ) ^ i := map_pow fr.κ fr.ζ i
    rw [h1, h2]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  have hmod : (fr.κ fr.ζ : E n) ^ i = (fr.κ fr.ζ : E n) ^ (i % orderOf fr.ζ) := by
    conv_lhs => rw [← Nat.div_add_mod i (orderOf fr.ζ), pow_add, pow_mul]
    rw [show (fr.κ fr.ζ : E n) ^ orderOf fr.ζ = 1 from by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]]
    rw [one_pow, one_mul]
  rw [hκ, hmod, fval_kapFX]
  ring

/-! ## The two field lemmas used in §2 (20) -/

/-- The recurrence `S_{j+2} = α₀ S_{j+1} + S_j` for `bS = S`. -/
lemma bS_rec {β α0 : E n} (hβ : β ≠ 0) (hβα : β + β⁻¹ = α0) (j : ℕ) :
    bS β (j + 2) = α0 * bS β (j + 1) + bS β j := by
  have e1 : β ^ (j + 2) = β ^ j * β ^ 2 := pow_add β j 2
  have e2 : β ^ (j + 1) = β ^ j * β := by rw [pow_add, pow_one]
  simp only [bS]
  rw [e1, e2, ← hβα]
  field_simp
  try ring_nf
  try simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  try ring

/-- `u_i² + α₀ u_i + 1 = w_i^{-1}` (used in §2 (20)). -/
lemma uSeq_sq_add_mul {β α0 : E n} (hβ : β ≠ 0) (hβα : β + β⁻¹ = α0) (hα0 : α0 ≠ 0)
    {i : ℕ} (hi : 1 ≤ i) (h : bS β i ≠ 0) :
    uSeq β i * uSeq β i + α0 * uSeq β i + 1 = (wSeq α0 β i)⁻¹ := by
  by_cases h2 : bS β (i + 1) = 0
  · have hbi : β ^ (i + 1) = 1 := (bS_eq_zero_iff β hβ (i + 1)).mp h2
    have hbi' : β ^ i = β⁻¹ := by
      have h := congrArg (fun z => z * β⁻¹) hbi
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ hβ, mul_one, one_mul] at h
      exact h
    have hSi : bS β i = α0 := by
      rw [bS, hbi', inv_inv, add_comm]; exact hβα
    have hprev : β ^ (i - 1) = β⁻¹ * β⁻¹ := by
      have h : β ^ (i - 1) * (β * β) = 1 := by
        rw [← pow_two, ← pow_add, show i - 1 + 2 = i + 1 by omega, hbi]
      rw [eq_inv_of_mul_eq_one_left h, mul_inv]
    have hS1 : bS β (i - 1) = α0 ^ 2 := by
      have h1 : bS β (i - 1) = β⁻¹ * β⁻¹ + β * β := by
        rw [bS, hprev, mul_inv]
        simp only [inv_inv]
      rw [h1]
      calc β⁻¹ * β⁻¹ + β * β = (β⁻¹ + β) ^ 2 := by rw [CharTwo.add_sq]; ring
        _ = α0 ^ 2 := by rw [add_comm, hβα]
    have hu : uSeq β i = α0 := by
      rw [uSeq_eq_div' β hβ hi, hS1, hSi]
      field_simp
    have hw : wSeq α0 β i = 1 := by
      rw [wSeq_eq, hSi, div_self hα0, one_pow]
    rw [hu, hw, inv_one]
    simp only [CharTwo.add_self_eq_zero, zero_add]
  · have hrec := uSeq_rec_alpha α0 β hβα hβ hi h h2
    have hdiv := uSeq_div α0 β hβα hβ hα0 hi h h2
    have hsum : uSeq β i + α0 = (uSeq β (i + 1))⁻¹ := by
      rw [← hrec]
      rw [show α0 + (uSeq β (i + 1))⁻¹ + α0 = (uSeq β (i + 1))⁻¹ + (α0 + α0) from by ring]
      rw [show (α0 : E n) + α0 = 0 from CharTwo.add_self_eq_zero α0, add_zero]
    have hstep : uSeq β i * uSeq β i + α0 * uSeq β i + 1
        = uSeq β i / uSeq β (i + 1) + 1 := by
      rw [show uSeq β i * uSeq β i + α0 * uSeq β i
          = uSeq β i * (uSeq β i + α0) from by ring, hsum, div_eq_mul_inv]
    rw [hstep, hdiv]
    rw [show (1 : E n) + 1 / wSeq α0 β i + 1 = 1 + 1 + 1 / wSeq α0 β i from by ring]
    rw [show (1 : E n) + 1 = 0 from CharTwo.add_self_eq_zero 1, zero_add, one_div]

/-- The two linear equations of §2 (20) solve for the shift and the `F*`-constant. -/
lemma shift_solvable {α0 A B s : E n} (hα0 : α0 ≠ 0) (hA : A ≠ 0)
    (hB : B ≠ 0) (hAα : A + α0 ≠ 0) (hBα : B + α0 ≠ 0)
    (hdisc : A * A + α0 * A + 1 ≠ 0)
    (h1 : α0 + A⁻¹ = A + s / B) (h2 : (A + α0)⁻¹ = A + s / (B + α0)) :
    B = A ∧ s = A * A + α0 * A + 1 := by
  have hf : s = B * (α0 + A⁻¹ + A) := by
    have h'a : (α0 + A⁻¹) * B = A * B + s := by
      have h := congrArg (fun z => z * B) h1
      simpa only [add_mul, div_mul_cancel₀ _ hB] using h
    have hs : s = (α0 + A⁻¹) * B + A * B := by
      rw [h'a]
      rw [show A * B + s + A * B = s + (A * B + A * B) from by ring,
        show A * B + A * B = 0 from CharTwo.add_self_eq_zero (A * B), add_zero]
    rw [hs]
    ring
  have hg : s = (B + α0) * (A + (A + α0)⁻¹) := by
    have h'b : (A + α0)⁻¹ * (B + α0) = A * (B + α0) + s := by
      have h := congrArg (fun z => z * (B + α0)) h2
      simpa only [add_mul, div_mul_cancel₀ _ hBα, inv_mul_cancel₀ hBα] using h
    have hs : s = (A + α0)⁻¹ * (B + α0) + A * (B + α0) := by
      rw [h'b]
      rw [show A * (B + α0) + s + A * (B + α0) = s + (A * (B + α0) + A * (B + α0)) from by ring,
        show A * (B + α0) + A * (B + α0) = 0 from CharTwo.add_self_eq_zero (A * (B + α0)), add_zero]
    rw [hs]
    try ring
  have hkey : B * (α0 + A⁻¹ + A) = (B + α0) * (A + (A + α0)⁻¹) := by rw [← hf, ← hg]
  have hmult := congrArg (fun z => z * (A * (A + α0))) hkey
  have e1 : B * (α0 + A⁻¹ + A) * (A * (A + α0))
      = B * (A * A + α0 * A + 1) * (A + α0) := by
    field_simp
    ring
  have e2 : (B + α0) * (A + (A + α0)⁻¹) * (A * (A + α0))
      = A * (A * A + α0 * A + 1) * (B + α0) := by
    field_simp
    try ring
  rw [e1, e2] at hmult
  have hBA : B * (A + α0) = A * (B + α0) := by
    have h3 : (A * A + α0 * A + 1) * (B * (A + α0))
        = (A * A + α0 * A + 1) * (A * (B + α0)) := by
      rw [show (A * A + α0 * A + 1) * (B * (A + α0))
          = B * (A * A + α0 * A + 1) * (A + α0) from by ring, hmult,
        show A * (A * A + α0 * A + 1) * (B + α0)
          = (A * A + α0 * A + 1) * (A * (B + α0)) from by ring]
    exact mul_left_cancel₀ hdisc h3
  have hαeq : B * α0 = A * α0 := by
    have h4 : A * B + B * α0 = A * B + A * α0 := by
      have h5 := hBA
      rw [mul_add, mul_add] at h5
      rw [mul_comm B A] at h5
      exact h5
    exact add_left_cancel h4
  have hBAeq : B = A := mul_right_cancel₀ hα0 hαeq
  refine ⟨hBAeq, ?_⟩
  rw [hf, hBAeq]
  field_simp
  ring
