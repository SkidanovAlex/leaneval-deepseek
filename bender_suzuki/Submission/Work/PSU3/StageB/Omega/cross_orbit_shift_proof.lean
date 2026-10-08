/-
# `Work.PSU3.StageB.Omega.cross_orbit_shift_proof` — Peterfalvi II Ch. VII §2 (20)

The cross-orbit translation identity.  The proof follows the reference: from the connecting
datum of §2 (7)+(8) (the unique fibre element with a `K`-witness), the sharp §2 (17) recursion
for `ω₁` and `ω₂`, the one-step computation §2 (19)a)/b) (`Omega.one_step`) and the coset
separation §2 (7) (`Omega.coset_sep_KW`) one obtains the two linear equations

  `α + x₁⁻¹ = x₁ + s (x₂+α)⁻¹`,   `(x₁+α)⁻¹ = x₁ + s x₂⁻¹`   (`s = nm(κ k)⁻¹`),

which solve (`shift_solvable`) to the base case `x₂ = x₁+α` and `s = x₁²+αx₁+1`.  Together with
the pure field identity `u_i² + α u_i + 1 = w_i⁻¹` (`uSeq_sq_add_mul`) this gives the `Q₀`-shift
of each one-step element, and the fibre is then matched witness-coset by witness-coset.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.Omega.beta_pow_setup
import Submission.Work.PSU3.StageB.Omega.beta_pow_m_eq_one
import Submission.Work.PSU3.StageB.Omega.orderOf_beta_eq
import Submission.Work.PSU3.StageB.Omega.fcan_zU_eq_vSeq
import Submission.Work.PSU3.StageB.Omega.cross_orbit_datum
import Submission.Work.PSU3.StageB.Omega.alpha_eq_of_two_orbits
import Submission.Work.PSU3.StageB.Omega.fcan_step10
import Submission.Work.PSU3.StageB.Omega.uSeq_div
import Submission.Work.PSU3.StageB.Omega.cross_orbit_shift_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- Two witnesses of the same `Q₀`-fibre element coincide. -/
lemma witness_unique (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω ω' : ↥Q} (hω' : (ω' : G) ∉ fr.Q0) {x : ↥Q} (hx : (x : G) ∈ fr.Q0)
    {d₁ d₂ : fr.KW} {y₁ y₂ : ↥Q} (hy₁ : (y₁ : G) ∈ fr.Q0) (hy₂ : (y₂ : G) ∈ fr.Q0)
    (h₁ : fcan hS.split (ω * x) =
      qconj hS.split ⟨(d₁ : G), fr.KW_le d₁.2⟩ (ω' * y₁))
    (h₂ : fcan hS.split (ω * x) =
      qconj hS.split ⟨(d₂ : G), fr.KW_le d₂.2⟩ (ω' * y₂)) :
    d₁ = d₂ ∧ y₁ = y₂ := by
  have heq : qconj hS.split ⟨(d₁ : G), fr.KW_le d₁.2⟩ (ω' * y₁) =
      qconj hS.split ⟨(d₂ : G), fr.KW_le d₂.2⟩ (ω' * y₂) := by rw [← h₁, h₂]
  have hbar : (fr.κ d₁ : E n) * Multiplicative.toAdd (fr.bar (ω' * y₁)) =
      (fr.κ d₂ : E n) * Multiplicative.toAdd (fr.bar (ω' * y₂)) := by
    have hh := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) heq
    rwa [qconj_toAdd_bar hS fr d₁ (ω' * y₁), qconj_toAdd_bar hS fr d₂ (ω' * y₂)] at hh
  simp only [map_mul, bar_eq_one_of_mem_Q0 fr hy₁, bar_eq_one_of_mem_Q0 fr hy₂, mul_one] at hbar
  have hb : Multiplicative.toAdd (fr.bar ω') ≠ 0 := toAdd_bar_ne_zero fr hω'
  have hκ : fr.κ d₁ = fr.κ d₂ := Units.ext (mul_right_cancel₀ hb hbar)
  have hd : d₁ = d₂ := fr.κ_injective hκ
  refine ⟨hd, ?_⟩
  rw [hd] at heq
  have h := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) heq
  rw [qconj_toAdd_bar hS fr d₂ (ω' * y₁), qconj_toAdd_bar hS fr d₂ (ω' * y₂)] at h
  have h2 := mul_left_cancel₀ (Units.ne_zero (fr.κ d₂)) h
  have h5 : ω' * y₁ = ω' * y₂ := by
    have h6 := congrArg (qconj hS.split (⟨(d₂ : G), fr.KW_le d₂.2⟩ : ↥(twoPoint H t))⁻¹) heq
    rw [qconj_mul', qconj_mul', mul_inv_cancel, qconj_one_eq, qconj_one_eq] at h6
    exact h6
  exact mul_left_cancel h5

/-- `zcQ` is injective on `σE`-fixed field elements. -/
lemma zcQ_inj' (fr : CoarseFrame H Q t n) {v w : E n} (hv : σE v = v) (hw : σE w = w)
    (h : zcQ fr v hv = zcQ fr w hw) : v = w :=
  fr.zc_inj v w hv hw (by simpa using congrArg (fun z : ↥Q => (z : G)) h)

/-- `zcQ` depends only on the field element. -/
lemma zcQ_congr (fr : CoarseFrame H Q t n) {v w : E n} (hv : σE v = v) (hw : σE w = w)
    (h : v = w) : zcQ fr v hv = zcQ fr w hw := by
  subst h
  exact Subtype.ext rfl

/-- If `κ d ∈ F*` then `d ∈ Ksub H t`. -/
lemma mem_Ksub_of_kappa_fx (fr : CoarseFrame H Q t n) {d : fr.KW} (u : ↥(FX n))
    (h : (fr.κ d : (E n)ˣ) = u.1) : (d : G) ∈ Ksub H t :=
  (fr.mem_K_iff d).mpr (by rw [h]; exact u.2)

/-- The field identity of §2 (20): the shift of the family-B coordinate. -/
lemma vSeq_shift_coord {n : ℕ} {α0 x1 x2 s u linv : E n} (hx : x2 = x1 + α0)
    (hs : s = x1 * x1 + α0 * x1 + 1) (hlin : linv = u * u + α0 * u + 1)
    (hD : x2 + u ≠ 0) :
    (u + α0) + linv * (x2 + u)⁻¹ = (x1 + s * (x2 + u)⁻¹) + α0 := by
  have hkey : linv + s = (u + x1) * (x2 + u) := by
    have h2 : (u + x1) * (x1 + α0 + u) = (u + x1) ^ 2 + (u + x1) * α0 := by ring
    rw [hlin, hs, hx, h2, CharTwo.add_sq]
    ring_nf
    simp only [CharTwo.two_eq_zero, zero_add]
  have hmain : (linv + s) * (x2 + u)⁻¹ = u + x1 := by
    rw [hkey, mul_assoc, mul_inv_cancel₀ hD, mul_one]
  have hgoal : u + linv * (x2 + u)⁻¹ = x1 + s * (x2 + u)⁻¹ := by
    have hsum : (u + linv * (x2 + u)⁻¹) + (x1 + s * (x2 + u)⁻¹) = 0 := by
      have h2 : (u + linv * (x2 + u)⁻¹) + (x1 + s * (x2 + u)⁻¹)
          = (u + x1) + (linv + s) * (x2 + u)⁻¹ := by ring
      rw [h2, hmain, CharTwo.add_self_eq_zero]
    exact CharTwo.add_eq_zero.mp hsum
  rw [show (u + α0) + linv * (x2 + u)⁻¹ = (u + linv * (x2 + u)⁻¹) + α0 from by ring, hgoal]

/-- The discriminant of the two §2 (20)-equations is nonzero. -/
lemma shift_disc_ne_zero {n : ℕ} {α0 A B s : E n} (hA : A ≠ 0) (hB : B ≠ 0) (hs : s ≠ 0)
    (h1 : α0 + A⁻¹ = A + s / B) : A * A + α0 * A + 1 ≠ 0 := by
  intro hc
  have hf : s = B * (α0 + A⁻¹ + A) := by
    have h'a : (α0 + A⁻¹) * B = A * B + s := by
      have h := congrArg (fun z => z * B) h1
      simpa only [add_mul, div_mul_cancel₀ _ hB] using h
    have hs' : s = (α0 + A⁻¹) * B + A * B := by
      rw [h'a]
      rw [show A * B + s + A * B = s + (A * B + A * B) from by ring,
        show A * B + A * B = 0 from CharTwo.add_self_eq_zero (A * B), add_zero]
    rw [hs']
    ring
  have hT : A + A⁻¹ + α0 = 0 := by
    have h0 : A * (A + A⁻¹ + α0) = 0 := by
      have h3 : A * (A + A⁻¹ + α0) = A * A + α0 * A + 1 := by
        rw [mul_add, mul_add, mul_inv_cancel₀ hA, mul_comm A α0]
        ring
      rw [h3, hc]
    exact (mul_eq_zero.mp h0).resolve_left hA
  have hT' : α0 + A⁻¹ + A = 0 := by
    rw [show α0 + A⁻¹ + A = A + A⁻¹ + α0 from by ring, hT]
  exact hs (by rw [hf, hT', mul_zero])

/-- `t`-conjugation is multiplicative on `G` (`t * t = 1`). -/
lemma t_mul_mul_t (hS : PSU3Hyp H Q t) (a b : G) :
    t * (a * b) * t = (t * a * t) * (t * b * t) := by
  obtain ht : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hS.split
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hconj : ∀ a : G, t * a * t = (MulAut.conj t) a := fun a => by
    rw [MulAut.conj_apply, htinv]
  calc t * (a * b) * t = (MulAut.conj t) (a * b) := hconj (a * b)
    _ = (MulAut.conj t) a * (MulAut.conj t) b := map_mul _ _ _
    _ = t * a * t * (t * b * t) := by rw [← hconj a, ← hconj b]

/-- `ζ` is fixed by `t`-conjugation, hence so are its powers. -/
lemma t_pow_zeta_t (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (i : ℕ) :
    t * (fr.ζ : G) ^ i * t = (fr.ζ : G) ^ i := by
  obtain ht : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hS.split
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hconj : ∀ a : G, t * a * t = (MulAut.conj t) a := fun a => by
    rw [MulAut.conj_apply, htinv]
  have h2 : (MulAut.conj t) (fr.ζ : G) = (fr.ζ : G) := by
    rw [← hconj, t_zeta_t hS.split fr]
  calc t * (fr.ζ : G) ^ i * t = (MulAut.conj t) ((fr.ζ : G) ^ i) := hconj _
    _ = ((MulAut.conj t) (fr.ζ : G)) ^ i := map_pow _ _ _
    _ = (fr.ζ : G) ^ i := by rw [h2]

theorem cross_orbit_shift_proof {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω₁ ω₂ : ↥Q} (h₁ : (ω₁ : G) ∉ fr.Q0) (h₂ : (ω₂ : G) ∉ fr.Q0)
    {α : ↥(Work.PSU3.StageB.FX n)}
    (hf₁ : Work.PSU3.StageB.fcan hS.split ω₁ =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω₁ * Work.PSU3.StageB.zcQF fr α))
    (hf₂ : Work.PSU3.StageB.fcan hS.split ω₂ =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω₂ * Work.PSU3.StageB.zcQF fr α))
    (horb : Multiplicative.toAdd (fr.bar ω₁) ∉
      Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω₂)))
    {x : ↥(Work.PSU3.StageB.FX n)}
    (hx : Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split (ω₁ * Work.PSU3.StageB.zcQF fr x))) ∈
      Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω₂))) :
    ∃ d : fr.KW, Work.PSU3.StageB.fcan hS.split (ω₁ * Work.PSU3.StageB.zcQF fr x) =
      Work.PSU3.StageB.qconj hS.split ⟨(d : G), fr.KW_le d.2⟩
        (ω₂ * Work.PSU3.StageB.zcQ fr (Work.PSU3.StageB.fval x + Work.PSU3.StageB.fval α)
          (by rw [map_add, x.2, α.2])) := by
  classical
  have hα0 : fval α ≠ 0 := Units.ne_zero α.1
  have hαfix : σE (fval α) = fval α := α.2
  have hzαQ : (zcQF fr α : G) ∈ fr.Q0 := by
    rw [zcQF_coe]; exact fr.zc_mem (fval α) hαfix
  have hω₁1 : (ω₁ : G) ≠ 1 := fun h => h₁ (by rw [h]; exact Q0_one_mem fr)
  have hω₂1 : (ω₂ : G) ≠ 1 := fun h => h₂ (by rw [h]; exact Q0_one_mem fr)
  -- ## 1. `bar (f ω₁) ∉ orbE (bar ω₂)`
  have hbar₁ : Multiplicative.toAdd (fr.bar (fcan hS.split ω₁)) ∉
      orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := by
    intro hcon
    have hmem1 : Multiplicative.toAdd (fr.bar (fcan hS.split ω₁)) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := by
      refine ⟨fr.ζ, ?_⟩
      have hbarζ : Multiplicative.toAdd
          (fr.bar (qconj hS.split (zetaD fr) (ω₁ * zcQF fr α))) =
          (fr.κ fr.ζ : E n) * Multiplicative.toAdd (fr.bar ω₁) := by
        rw [show qconj hS.split (zetaD fr) (ω₁ * zcQF fr α) =
            qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ (ω₁ * zcQF fr α) from rfl,
          qconj_mul_apply]
        have hz : qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ (zcQF fr α) = zcQF fr α := by
          apply Subtype.ext
          rw [qconj_coe]
          exact fr.act_zc_ζ (fval α) α.2
        rw [hz, map_mul, bar_eq_one_of_mem_Q0 fr hzαQ, mul_one]
        exact fr.act_bar fr.ζ ω₁ (qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ ω₁)
          (by rw [qconj_coe])
      rw [hf₁]
      exact hbarζ
    have he1 : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split ω₁))) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := orbE_eq_of_mem fr hmem1
    have he2 : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split ω₁))) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := orbE_eq_of_mem fr hcon
    exact horb (by rw [← he1.symm.trans he2]; exact orbE_refl fr _)
  -- ## 2. the connecting datum of §2 (7)+(8)
  have hcard := cross_orbit_card hS fr h₁ h₂ horb
  obtain ⟨x₁, y₂, hx₁Q, hy₂Q, k, hkK, hψ⟩ := exists_Ksub_witness_of_card hS fr h₁ h₂ hcard
  have hx₁1 : x₁ ≠ 1 := by
    intro hxeq
    exact hbar₁ (by simpa [hxeq] using orbE_of_cntSet hS fr hx₁Q hy₂Q hψ)
  obtain ⟨X₁, hX₁⟩ := exists_zcQF_eq_of_mem_Q0 fr hx₁Q hx₁1
  -- `y₂ ≠ 1` (the shift of the `K`-witness is non-trivial)
  have hω₂bar : Multiplicative.toAdd (fr.bar (fcan hS.split ω₂)) =
      (fr.κ fr.ζ : E n) * Multiplicative.toAdd (fr.bar ω₂) := by
    have hq := qconj_toAdd_bar hS fr fr.ζ (ω₂ * zcQF fr α)
    rw [show qconj hS.split (zetaD fr) (ω₂ * zcQF fr α) =
        qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ (ω₂ * zcQF fr α) from rfl] at hf₂
    rw [hf₂, hq, map_mul, bar_eq_one_of_mem_Q0 fr hzαQ, mul_one]
  have hy₂1 : y₂ ≠ 1 := by
    intro hyeq
    apply horb
    rw [mem_orbE_iff]
    refine ⟨k⁻¹ * fr.ζ, ?_⟩
    have hψ1 : fcan hS.split (ω₁ * x₁) =
        qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ ω₂ := by
      rw [hψ, hyeq, mul_one]
    have hne : (ω₁ * x₁ : ↥Q) ≠ 1 := by
      intro hc
      have hb : fr.bar (ω₁ * x₁) = 1 := (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
      rw [map_mul, bar_eq_one_of_mem_Q0 fr hx₁Q, mul_one] at hb
      exact bar_ne_one_of_not_mem_Q0 fr h₁ hb
    have h1 : (ω₁ * x₁ : ↥Q) = fcan hS.split
        (qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ ω₂) := by
      rw [← hψ1]
      exact Subtype.ext (fcan_fcan hS.split (fun h => hne (Subtype.ext h))).1.symm
    have h2 := fcan_qconj hS.split hω₂1 ⟨(k : G), fr.KW_le k.2⟩
    have h3 : t * ((⟨(k : G), fr.KW_le k.2⟩ : ↥(twoPoint H t)) : G) * t = (k : G)⁻¹ :=
      tconj_eq_inv hS.split fr hkK
    have h4 : fcan hS.split (qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ ω₂) =
        qconj hS.split ⟨((k⁻¹ : fr.KW) : G), fr.KW_le (k⁻¹).2⟩ (fcan hS.split ω₂) := by
      apply Subtype.ext
      rw [qconj_coe, h2, h3, Subgroup.coe_inv]
      try rfl
    have h5 : fr.bar ω₁ = fr.bar (fcan hS.split
        (qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ ω₂)) := by
      rw [← h1, map_mul, bar_eq_one_of_mem_Q0 fr hx₁Q, mul_one]
    rw [h5, h4, qconj_toAdd_bar hS fr (k⁻¹) (fcan hS.split ω₂), hω₂bar, map_mul,
      Units.val_mul]
    ring
  obtain ⟨Y₂, hY₂⟩ := exists_zcQF_eq_of_mem_Q0 fr hy₂Q hy₂1
  have hψ' : fcan hS.split (ω₁ * zcQF fr X₁) =
      qconj hS.split (⟨(k : G), fr.KW_le k.2⟩ : ↥(twoPoint H t)) (ω₂ * zcQF fr Y₂) := by
    rw [← hX₁, ← hY₂] at hψ
    exact hψ
  -- ## 3. the §2 (17) data
  have hn1 : 1 ≤ n := (omega_card_facts hS fr).1
  obtain ⟨β, hβ, hβα, hσ₀⟩ := exists_beta hn1 (fval α) hαfix
  have hσ : σE β = β ∨ σE β = β⁻¹ :=
    hσ₀.elim (fun h => Or.inr h) (fun h => Or.inl h)
  have hmpos : 1 ≤ orderOf fr.ζ :=
    Nat.one_le_iff_ne_zero.mpr (orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite fr.ζ))
  have hN : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → bS β i ≠ 0 := by
    intro i hi hile
    exact bS_ne_zero_of_lt_orderOf hS fr h₁ hf₁ hβ hβα i hi (by omega)
  set lam : ℕ → ↥(FX n) := lamSeq (fval α) β hαfix hσ with hlamdef
  have hlam : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → fval (lam i) = wSeq (fval α) β i :=
    fun i hi hile => by
      rw [hlamdef]
      exact fval_lamSeq (fval α) β hαfix hσ
        (wSeq_ne_zero (fval α) β hα0 i (hN i hi hile))
  have h17₁ := fcan_zU_eq_vSeq hS fr h₁ hf₁ hβ hσ hβα lam hlam hN
  have h17₂ := fcan_zU_eq_vSeq hS fr h₂ hf₂ hβ hσ hβα lam hlam hN
  have hzQ : ∀ u : ↥(FX n), (zcQF fr u : G) ∈ fr.Q0 := fun u => by
    rw [zcQF_coe]; exact fr.zc_mem (fval u) u.2
  -- ## 4. side conditions and the `(19)` one-step elements
  have hψrev : fcan hS.split (ω₂ * zcQF fr Y₂) =
      qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₁ * zcQF fr X₁) := by
    have hne : (ω₁ * zcQF fr X₁ : ↥Q) ≠ 1 := by
      intro hc
      have hb : fr.bar (ω₁ * zcQF fr X₁) = 1 :=
        (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
      rw [map_mul, bar_eq_one_of_mem_Q0 fr (hzQ X₁), mul_one] at hb
      exact bar_ne_one_of_not_mem_Q0 fr h₁ hb
    have hz : (ω₂ * zcQF fr Y₂ : ↥Q) ≠ 1 := by
      intro hc
      have hb : fr.bar (ω₂ * zcQF fr Y₂) = 1 :=
        (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
      rw [map_mul, bar_eq_one_of_mem_Q0 fr (hzQ Y₂), mul_one] at hb
      exact bar_ne_one_of_not_mem_Q0 fr h₂ hb
    have h1 : (ω₁ * zcQF fr X₁ : ↥Q) = fcan hS.split
        (qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₂ * zcQF fr Y₂)) := by
      rw [← hψ']
      exact Subtype.ext (fcan_fcan hS.split (fun h => hne (Subtype.ext h))).1.symm
    have h2 := fcan_qconj hS.split (fun h => hz (Subtype.ext h)) ⟨(k : G), fr.KW_le k.2⟩
    have h3 : t * ((⟨(k : G), fr.KW_le k.2⟩ : ↥(twoPoint H t)) : G) * t = (k : G)⁻¹ :=
      tconj_eq_inv hS.split fr hkK
    have h4 : fcan hS.split (qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₂ * zcQF fr Y₂)) =
        qconj hS.split ⟨((k⁻¹ : fr.KW) : G), fr.KW_le (k⁻¹).2⟩
          (fcan hS.split (ω₂ * zcQF fr Y₂)) := by
      apply Subtype.ext
      rw [qconj_coe, h2, h3, Subgroup.coe_inv]
      try rfl
    have h5 : qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₁ * zcQF fr X₁) =
        fcan hS.split (ω₂ * zcQF fr Y₂) := by
      have h6 : qconj hS.split ⟨(k : G), fr.KW_le k.2⟩
          (qconj hS.split ⟨((k⁻¹ : fr.KW) : G), fr.KW_le (k⁻¹).2⟩
            (fcan hS.split (ω₂ * zcQF fr Y₂))) = fcan hS.split (ω₂ * zcQF fr Y₂) := by
        rw [qconj_mul']
        have h7 : (⟨((k⁻¹ : fr.KW) : G), fr.KW_le (k⁻¹).2⟩ : ↥(twoPoint H t)) *
            ⟨(k : G), fr.KW_le k.2⟩ = 1 := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_one, Subgroup.coe_inv]
          exact inv_mul_cancel (k : G)
        rw [h7, qconj_one_eq]
      rw [← h6, ← h4, h1]
    exact h5.symm
  -- the `Q₀`-membership of the `(17)`-shift
  have hvfix : ∀ i, σE (vSeq (fval α) β i) = vSeq (fval α) β i := fun i => by
    show σE (uSeq β i + fval α) = uSeq β i + fval α
    rw [map_add, uSeq_fixed β hβ hσ i, α.2]
  have hvQ : ∀ i, (zcQ fr (vSeq (fval α) β i) (hvfix i) : G) ∈ fr.Q0 := fun i => by
    rw [zcQ_coe]; exact fr.zc_mem _ (hvfix i)
  have hsideA : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → fval X₁ + uSeq β i ≠ 0 := by
    intro i hi hile hcon
    have hcons : uSeq β i = fval X₁ := by
      have h := eq_neg_of_add_eq_zero_left hcon
      simpa only [CharTwo.neg_eq] using h.symm
    have hz : zU fr β hβ hσ i = zcQF fr X₁ := by
      apply Subtype.ext
      rw [zU_coe, zcQF_coe, hcons]
    have hrel := h17₁ i hi hile
    rw [hz] at hrel
    have heq : qconj hS.split ⟨(dSeq hS fr lam i : fr.KW), fr.KW_le (dSeq hS fr lam i).2⟩
          (ω₁ * zcQ fr (vSeq (fval α) β i) (hvfix i)) =
        qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₂ * zcQF fr Y₂) := by
      rw [← hrel, hψ']
    have hbar := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) heq
    rw [qconj_toAdd_bar hS fr (dSeq hS fr lam i) (ω₁ * zcQ fr (vSeq (fval α) β i) (hvfix i)),
      qconj_toAdd_bar hS fr k (ω₂ * zcQF fr Y₂)] at hbar
    simp only [map_mul, bar_eq_one_of_mem_Q0 fr (hvQ i), mul_one,
      bar_eq_one_of_mem_Q0 fr (hzQ Y₂)] at hbar
    -- `hbar : κ (dSeq …) · bar ω₁ = κ k · bar ω₂`
    apply horb
    rw [mem_orbE_iff]
    refine ⟨(dSeq hS fr lam i)⁻¹ * k, ?_⟩
    have key : Multiplicative.toAdd (fr.bar ω₁) =
        (fr.κ (dSeq hS fr lam i) : E n)⁻¹
          * ((fr.κ k : E n) * Multiplicative.toAdd (fr.bar ω₂)) := by
      calc Multiplicative.toAdd (fr.bar ω₁)
          = (fr.κ (dSeq hS fr lam i) : E n)⁻¹
            * ((fr.κ (dSeq hS fr lam i) : E n) * Multiplicative.toAdd (fr.bar ω₁)) := by
            rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero (fr.κ (dSeq hS fr lam i))), one_mul]
        _ = (fr.κ (dSeq hS fr lam i) : E n)⁻¹
            * ((fr.κ k : E n) * Multiplicative.toAdd (fr.bar ω₂)) := by
            rw [← hbar]
    rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val]
    rw [key]
    ring
  have hsideB : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → fval Y₂ + uSeq β i ≠ 0 := by
    intro i hi hile hcon
    have hcons : uSeq β i = fval Y₂ := by
      have h := eq_neg_of_add_eq_zero_left hcon
      simpa only [CharTwo.neg_eq] using h.symm
    have hz : zU fr β hβ hσ i = zcQF fr Y₂ := by
      apply Subtype.ext
      rw [zU_coe, zcQF_coe, hcons]
    have hrel := h17₂ i hi hile
    rw [hz] at hrel
    have heq : qconj hS.split ⟨(dSeq hS fr lam i : fr.KW), fr.KW_le (dSeq hS fr lam i).2⟩
          (ω₂ * zcQ fr (vSeq (fval α) β i) (hvfix i)) =
        qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₁ * zcQF fr X₁) := by
      rw [← hrel, hψrev]
    have hbar := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) heq
    rw [qconj_toAdd_bar hS fr (dSeq hS fr lam i) (ω₂ * zcQ fr (vSeq (fval α) β i) (hvfix i)),
      qconj_toAdd_bar hS fr k (ω₁ * zcQF fr X₁)] at hbar
    simp only [map_mul, bar_eq_one_of_mem_Q0 fr (hvQ i), mul_one,
      bar_eq_one_of_mem_Q0 fr (hzQ X₁)] at hbar
    -- `hbar : κ (dSeq …) · bar ω₂ = κ k · bar ω₁`
    apply horb
    rw [mem_orbE_iff]
    refine ⟨k⁻¹ * dSeq hS fr lam i, ?_⟩
    have key : Multiplicative.toAdd (fr.bar ω₁) =
        (fr.κ k : E n)⁻¹
          * ((fr.κ (dSeq hS fr lam i) : E n) * Multiplicative.toAdd (fr.bar ω₂)) := by
      calc Multiplicative.toAdd (fr.bar ω₁)
          = (fr.κ k : E n)⁻¹ * ((fr.κ k : E n) * Multiplicative.toAdd (fr.bar ω₁)) := by
            rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero (fr.κ k)), one_mul]
        _ = (fr.κ k : E n)⁻¹
            * ((fr.κ (dSeq hS fr lam i) : E n) * Multiplicative.toAdd (fr.bar ω₂)) := by
            rw [← hbar]
    rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val]
    rw [key]
    ring
  -- ## 5. the `(19)` one-step data
  have hUB : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → fval Y₂ + uSeq β i ≠ 0 := hsideB
  set UB : ℕ → ↥(FX n) := fun i =>
    if h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1 then
      mkFX (fval Y₂ + uSeq β i) (by rw [map_add, Y₂.2, uSeq_fixed β hβ hσ i]) (hUB i h.1 h.2)
    else 1 with hUBdef
  have hUBf : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1),
      fval (UB i) = fval Y₂ + uSeq β i := by
    intro i h
    rw [hUBdef]
    simp only [dif_pos h]
    rfl
  have hsB : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      σE (fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB i))⁻¹)
        = fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB i))⁻¹ := fun i _ _ => by
    rw [map_add, X₁.2, map_mul, map_inv₀, (nmF fr (kapFX fr hkK)).2, map_inv₀, (UB i).2]
  have hsB' : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      σE (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UB i))⁻¹)
        = vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UB i))⁻¹ := fun i _ _ => by
    rw [map_add, hvfix i, map_mul, map_inv₀, (lam i).2, map_inv₀, (UB i).2]
  -- the family-B candidate `ω₁ · zc w_i` with shift `ω₂ · zc x_i`
  set wB : ℕ → ↥Q := fun i => if h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1 then
      zcQ fr (fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB i))⁻¹) (hsB i h.1 h.2)
    else 1 with hwBdef
  set xB : ℕ → ↥Q := fun i => if h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1 then
      zcQ fr (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UB i))⁻¹) (hsB' i h.1 h.2)
    else 1 with hxBdef
  have hwBcoe : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1),
      (wB i : G) = fr.zc (fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB i))⁻¹) := by
    intro i h
    rw [hwBdef]; simp only [dif_pos h]; exact zcQ_coe fr _ _
  have hxBcoe : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1),
      (xB i : G) = fr.zc (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UB i))⁻¹) := by
    intro i h
    rw [hxBdef]; simp only [dif_pos h]; exact zcQ_coe fr _ _
  have hB : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      fcan hS.split (ω₁ * wB i) =
        qconj hS.split
          ⟨((dSeq hS fr lam i * kElF fr (tau hS fr (UB i)) ^ 2 * k : fr.KW) : G),
            fr.KW_le (dSeq hS fr lam i * kElF fr (tau hS fr (UB i)) ^ 2 * k).2⟩
          (ω₂ * xB i) := by
    intro i hi hile
    have hzUB : (zcQF fr Y₂ * zcQF fr (UB i) : ↥Q) = zU fr β hβ hσ i := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, zcQF_coe, zcQF_coe, zU_coe, hUBf i ⟨hi, hile⟩]
      rw [← fr.zc_add (fval Y₂) (fval Y₂ + uSeq β i) Y₂.2
        (by rw [map_add, Y₂.2, uSeq_fixed β hβ hσ i])]
      congr 1
      rw [← add_assoc, CharTwo.add_self_eq_zero (fval Y₂), zero_add]
    have hseq : fcan hS.split (ω₂ * zcQF fr Y₂ * zcQF fr (UB i)) =
        qconj hS.split ⟨(dSeq hS fr lam i : fr.KW), fr.KW_le (dSeq hS fr lam i).2⟩
          (ω₂ * zcQ fr (vSeq (fval α) β i) (hvfix i)) := by
      rw [mul_assoc, hzUB]
      exact h17₂ i hi hile
    have hmain := one_step hS fr h₂ h₁ (hzQ Y₂) (hzQ X₁) hkK hψrev (hvQ i) hseq
    have hL1 : (zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr (UB i)⁻¹) : ↥Q) =
        zcQ fr (fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB i))⁻¹)
          (hsB i hi hile) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, kact_kapFX_inv_coe hS fr hkK (UB i)⁻¹, zcQF_coe, zcQ_coe,
        fval_inv, ← fr.zc_add (fval X₁) ((fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB i))⁻¹)
          X₁.2 (by rw [map_mul, map_inv₀, (nmF fr (kapFX fr hkK)).2, map_inv₀, (UB i).2])]
    have hL2 : zcQ fr (fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB i))⁻¹)
        (hsB i hi hile) = wB i := by
      apply Subtype.ext
      rw [zcQ_coe, hwBcoe i ⟨hi, hile⟩]
    have hL : (ω₁ * zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr (UB i)⁻¹) : ↥Q) = ω₁ * wB i := by
      rw [mul_assoc, hL1.trans hL2]
    have hR1 : (zcQ fr (vSeq (fval α) β i) (hvfix i)
          * kact hS fr (dSeq hS fr lam i)⁻¹ (zcQF fr (UB i)⁻¹) : ↥Q) =
        zcQ fr (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UB i))⁻¹)
          (hsB' i hi hile) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, kact_dSeq_inv_coe hS fr lam i (UB i)⁻¹, zcQ_coe, zcQ_coe,
        fval_inv, ← fr.zc_add (vSeq (fval α) β i) ((fval (lam i))⁻¹ * (fval (UB i))⁻¹)
          (hvfix i) (by rw [map_mul, map_inv₀, (lam i).2, map_inv₀, (UB i).2])]
    have hR2 : zcQ fr (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UB i))⁻¹)
        (hsB' i hi hile) = xB i := by
      apply Subtype.ext
      rw [zcQ_coe, hxBcoe i ⟨hi, hile⟩]
    have hR : (ω₂ * zcQ fr (vSeq (fval α) β i) (hvfix i)
          * kact hS fr (dSeq hS fr lam i)⁻¹ (zcQF fr (UB i)⁻¹) : ↥Q) = ω₂ * xB i := by
      rw [mul_assoc, hR1.trans hR2]
    rw [hL, hR] at hmain
    exact hmain
  -- the `ζ`-coset of the family-B exponent
  have hBcoset : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      ∃ h : ↥(FX n), (fr.κ (dSeq hS fr lam i * kElF fr (tau hS fr (UB i)) ^ 2 * k) : (E n)ˣ)
        = (fr.κ fr.ζ) ^ i * h.1 := by
    intro i hi hile
    refine ⟨tau hS fr (lam i) * (tau hS fr (UB i)) ^ 2 * kapFX fr hkK, Units.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow, dSeq_kappa, kElF_kappa,
      Units.val_mul, Units.val_pow_eq_pow_val, fval_kapFX]
    ring
  -- the `u`-elements `UA i = zc⁻¹(x₁ + u_i)` for family A
  have hUA : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → fval X₁ + uSeq β i ≠ 0 := hsideA
  set UA : ℕ → ↥(FX n) := fun i =>
    if h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1 then
      mkFX (fval X₁ + uSeq β i) (by rw [map_add, X₁.2, uSeq_fixed β hβ hσ i]) (hUA i h.1 h.2)
    else 1 with hUAdef
  have hUAf : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1),
      fval (UA i) = fval X₁ + uSeq β i := by
    intro i h
    rw [hUAdef]
    simp only [dif_pos h]
    rfl
  have hsA : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      σE (fval Y₂ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UA i))⁻¹)
        = fval Y₂ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UA i))⁻¹ := fun i _ _ => by
    rw [map_add, Y₂.2, map_mul, map_inv₀, (nmF fr (kapFX fr hkK)).2, map_inv₀, (UA i).2]
  have hsA' : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      σE (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UA i))⁻¹)
        = vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UA i))⁻¹ := fun i _ _ => by
    rw [map_add, hvfix i, map_mul, map_inv₀, (lam i).2, map_inv₀, (UA i).2]
  set xA : ℕ → ↥Q := fun i => if h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1 then
      zcQ fr (fval Y₂ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UA i))⁻¹) (hsA i h.1 h.2)
    else 1 with hxAdef
  set wA : ℕ → ↥Q := fun i => if h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1 then
      zcQ fr (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UA i))⁻¹) (hsA' i h.1 h.2)
    else 1 with hwAdef
  have hxAcoe : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1),
      (xA i : G) = fr.zc (fval Y₂ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UA i))⁻¹) := by
    intro i h
    rw [hxAdef]; simp only [dif_pos h]; exact zcQ_coe fr _ _
  have hwAcoe : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1),
      (wA i : G) = fr.zc (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UA i))⁻¹) := by
    intro i h
    rw [hwAdef]; simp only [dif_pos h]; exact zcQ_coe fr _ _
  -- family A: `f (ω₂ zc xa_i) = (ω₁ zc wa_i)^{E_i}`
  have hA : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      fcan hS.split (ω₂ * xA i) =
        qconj hS.split
          ⟨((dSeq hS fr lam i * kElF fr (tau hS fr (UA i)) ^ 2 * k : fr.KW) : G),
            fr.KW_le (dSeq hS fr lam i * kElF fr (tau hS fr (UA i)) ^ 2 * k).2⟩
          (ω₁ * wA i) := by
    intro i hi hile
    have hzUA : (zcQF fr X₁ * zcQF fr (UA i) : ↥Q) = zU fr β hβ hσ i := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, zcQF_coe, zcQF_coe, zU_coe, hUAf i ⟨hi, hile⟩]
      rw [← fr.zc_add (fval X₁) (fval X₁ + uSeq β i) X₁.2
        (by rw [map_add, X₁.2, uSeq_fixed β hβ hσ i])]
      congr 1
      rw [← add_assoc, CharTwo.add_self_eq_zero (fval X₁), zero_add]
    have hseq : fcan hS.split (ω₁ * zcQF fr X₁ * zcQF fr (UA i)) =
        qconj hS.split ⟨(dSeq hS fr lam i : fr.KW), fr.KW_le (dSeq hS fr lam i).2⟩
          (ω₁ * zcQ fr (vSeq (fval α) β i) (hvfix i)) := by
      rw [mul_assoc, hzUA]
      exact h17₁ i hi hile
    have hmain := one_step hS fr h₁ h₂ (hzQ X₁) (hzQ Y₂) hkK hψ' (hvQ i) hseq
    have hL1 : (zcQF fr Y₂ * kact hS fr k⁻¹ (zcQF fr (UA i)⁻¹) : ↥Q) =
        zcQ fr (fval Y₂ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UA i))⁻¹)
          (hsA i hi hile) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, kact_kapFX_inv_coe hS fr hkK (UA i)⁻¹, zcQF_coe, zcQ_coe,
        fval_inv, ← fr.zc_add (fval Y₂) ((fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UA i))⁻¹)
          Y₂.2 (by rw [map_mul, map_inv₀, (nmF fr (kapFX fr hkK)).2, map_inv₀, (UA i).2])]
    have hL2 : zcQ fr (fval Y₂ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UA i))⁻¹)
        (hsA i hi hile) = xA i := by
      apply Subtype.ext
      rw [zcQ_coe, hxAcoe i ⟨hi, hile⟩]
    have hL : (ω₂ * zcQF fr Y₂ * kact hS fr k⁻¹ (zcQF fr (UA i)⁻¹) : ↥Q) = ω₂ * xA i := by
      rw [mul_assoc, hL1.trans hL2]
    have hR1 : (zcQ fr (vSeq (fval α) β i) (hvfix i)
          * kact hS fr (dSeq hS fr lam i)⁻¹ (zcQF fr (UA i)⁻¹) : ↥Q) =
        zcQ fr (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UA i))⁻¹)
          (hsA' i hi hile) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, kact_dSeq_inv_coe hS fr lam i (UA i)⁻¹, zcQ_coe, zcQ_coe,
        fval_inv, ← fr.zc_add (vSeq (fval α) β i) ((fval (lam i))⁻¹ * (fval (UA i))⁻¹)
          (hvfix i) (by rw [map_mul, map_inv₀, (lam i).2, map_inv₀, (UA i).2])]
    have hR2 : zcQ fr (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UA i))⁻¹)
        (hsA' i hi hile) = wA i := by
      apply Subtype.ext
      rw [zcQ_coe, hwAcoe i ⟨hi, hile⟩]
    have hR : (ω₁ * zcQ fr (vSeq (fval α) β i) (hvfix i)
          * kact hS fr (dSeq hS fr lam i)⁻¹ (zcQF fr (UA i)⁻¹) : ↥Q) = ω₁ * wA i := by
      rw [mul_assoc, hR1.trans hR2]
    rw [hL, hR] at hmain
    exact hmain
  -- the `Q₀`-memberships of the four families of arguments
  have hxAQ : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1), (xA i : G) ∈ fr.Q0 := by
    intro i h; rw [hxAcoe i h]; exact fr.zc_mem _ (hsA i h.1 h.2)
  have hwAQ : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1), (wA i : G) ∈ fr.Q0 := by
    intro i h; rw [hwAcoe i h]; exact fr.zc_mem _ (hsA' i h.1 h.2)
  have hxBQ : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1), (xB i : G) ∈ fr.Q0 := by
    intro i h; rw [hxBcoe i h]; exact fr.zc_mem _ (hsB' i h.1 h.2)
  have hwBQ : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1), (wB i : G) ∈ fr.Q0 := by
    intro i h; rw [hwBcoe i h]; exact fr.zc_mem _ (hsB i h.1 h.2)
  -- ## 6.  the family-A reversal: `E_i = (t · D_i · t)⁻¹`
  set Kp : ℕ → fr.KW := fun i =>
    kElF fr (tau hS fr (lam i)) * kElF fr (tau hS fr (UA i)) ^ 2 * k with hKpdef
  have hkKp : ∀ i, ((Kp i : fr.KW) : G) ∈ Ksub H t := by
    intro i
    have h1 : ((Kp i : fr.KW) : G) = (kElF fr (tau hS fr (lam i)) : G) *
        ((kElF fr (tau hS fr (UA i)) : fr.KW) : G) ^ 2 * (k : G) := by
      rw [hKpdef]; simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    rw [h1]
    exact (Ksub H t).mul_mem ((Ksub H t).mul_mem
      (kElF_mem_Ksub fr (tau hS fr (lam i)))
      ((Ksub H t).pow_mem (kElF_mem_Ksub fr (tau hS fr (UA i))) 2)) hkK
  set EE : ℕ → fr.KW := fun i => Kp i * (fr.ζ ^ i)⁻¹ with hEEdef
  have hEEinv : ∀ i, ((EE i)⁻¹ : fr.KW) = fr.ζ ^ i * (Kp i)⁻¹ := by
    intro i; rw [hEEdef]; group
  have hD_eq : ∀ i, (dSeq hS fr lam i * kElF fr (tau hS fr (UA i)) ^ 2 * k : fr.KW)
      = fr.ζ ^ i * Kp i := by
    intro i
    rw [hKpdef]
    rw [show dSeq hS fr lam i = fr.ζ ^ i * kElF fr (tau hS fr (lam i)) from rfl]
    group
  have hEcoe : ∀ i, (((EE i)⁻¹ : fr.KW) : G)
      = t * ((dSeq hS fr lam i * kElF fr (tau hS fr (UA i)) ^ 2 * k : fr.KW) : G) * t := by
    intro i
    have hL : (((EE i)⁻¹ : fr.KW) : G) = (fr.ζ : G) ^ i * (((Kp i)⁻¹ : fr.KW) : G) := by
      rw [hEEinv i, Subgroup.coe_mul, Subgroup.coe_pow]
    have hkp : t * ((Kp i : fr.KW) : G) * t = (((Kp i)⁻¹ : fr.KW) : G) := by
      rw [Subgroup.coe_inv]
      exact tconj_eq_inv hS.split fr (hkKp i)
    rw [hL, hD_eq i, Subgroup.coe_mul, Subgroup.coe_pow,
      t_mul_mul_t hS ((fr.ζ : G) ^ i) ((Kp i : fr.KW) : G), t_pow_zeta_t hS fr i, hkp]
  have hneX : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → ((ω₂ * xA i : ↥Q) : G) ≠ 1 := by
    intro i hi hile hc
    have hb : fr.bar (ω₂ * xA i) = 1 :=
      (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
    rw [map_mul, bar_eq_one_of_mem_Q0 fr (hxAQ i ⟨hi, hile⟩), mul_one] at hb
    exact bar_ne_one_of_not_mem_Q0 fr h₂ hb
  have hneW : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → ((ω₁ * wA i : ↥Q) : G) ≠ 1 := by
    intro i hi hile hc
    have hb : fr.bar (ω₁ * wA i) = 1 :=
      (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
    rw [map_mul, bar_eq_one_of_mem_Q0 fr (hwAQ i ⟨hi, hile⟩), mul_one] at hb
    exact bar_ne_one_of_not_mem_Q0 fr h₁ hb
  have hEA : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      ∃ Ee : fr.KW, fcan hS.split (ω₁ * wA i) =
        qconj hS.split ⟨(Ee : G), fr.KW_le Ee.2⟩ (ω₂ * xA i) := by
    intro i hi hile
    exact ⟨EE i,
      fcan_qconj_rev hS fr (hneX i hi hile) (hneW i hi hile) (hEcoe i) (hA i hi hile)⟩
  have hWcoset : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      ∃ h : ↥(FX n), (fr.κ (EE i) : (E n)ˣ) * (fr.κ fr.ζ) ^ i = h.1 := by
    intro i hi hile
    refine ⟨kapFX fr (hkKp i), ?_⟩
    show fr.κ (EE i) * (fr.κ fr.ζ) ^ i = fr.κ (Kp i)
    rw [hEEdef]
    show fr.κ (Kp i * (fr.ζ ^ i)⁻¹) * (fr.κ fr.ζ) ^ i = fr.κ (Kp i)
    rw [map_mul, map_inv, map_pow]
    group
  -- ## 7.  the §2 (7) coset comparison: `wA i = wB (m - i)`
  have hcoset : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      wA i = wB (orderOf fr.ζ - i) := by
    intro i hi hile
    have hj1 : 1 ≤ orderOf fr.ζ - i := by omega
    have hjm : orderOf fr.ζ - i ≤ orderOf fr.ζ - 1 := by omega
    have hEAi : fcan hS.split (ω₁ * wA i) =
        qconj hS.split ⟨(EE i : G), fr.KW_le (EE i).2⟩ (ω₂ * xA i) :=
      fcan_qconj_rev hS fr (hneX i hi hile) (hneW i hi hile) (hEcoe i) (hA i hi hile)
    have hKsub : (EE i : G)⁻¹ *
        ((dSeq hS fr lam (orderOf fr.ζ - i) *
          kElF fr (tau hS fr (UB (orderOf fr.ζ - i))) ^ 2 * k : fr.KW) : G) ∈ Ksub H t := by
      obtain ⟨gA, hgA⟩ := hWcoset i hi hile
      obtain ⟨gB, hgB⟩ := hBcoset (orderOf fr.ζ - i) hj1 hjm
      have hgA' : fr.κ (EE i) = gA.1 * ((fr.κ fr.ζ) ^ i)⁻¹ := by
        have h := congrArg (fun z => z * ((fr.κ fr.ζ) ^ i)⁻¹) hgA
        simp only [mul_assoc, mul_inv_cancel, mul_one] at h
        exact h
      have hcc : (fr.κ fr.ζ) ^ i * (fr.κ fr.ζ) ^ (orderOf fr.ζ - i) = 1 := by
        rw [← pow_add, show i + (orderOf fr.ζ - i) = orderOf fr.ζ from by omega, ← map_pow,
          pow_orderOf_eq_one, map_one]
      have hκ : (fr.κ ((EE i)⁻¹ * (dSeq hS fr lam (orderOf fr.ζ - i) *
            kElF fr (tau hS fr (UB (orderOf fr.ζ - i))) ^ 2 * k) : fr.KW) : (E n)ˣ)
          = (gA⁻¹ * gB).1 := by
        rw [map_mul, map_inv, hgA', hgB]
        calc (gA.1 * ((fr.κ fr.ζ) ^ i)⁻¹)⁻¹
              * ((fr.κ fr.ζ) ^ (orderOf fr.ζ - i) * gB.1)
            = ((fr.κ fr.ζ) ^ i * (gA.1)⁻¹) * ((fr.κ fr.ζ) ^ (orderOf fr.ζ - i) * gB.1) := by
              rw [mul_inv_rev, inv_inv]
          _ = (gA.1)⁻¹ * gB.1 := by
              rw [show ((fr.κ fr.ζ) ^ i * (gA.1)⁻¹)
                    * ((fr.κ fr.ζ) ^ (orderOf fr.ζ - i) * gB.1)
                  = ((fr.κ fr.ζ) ^ i * (fr.κ fr.ζ) ^ (orderOf fr.ζ - i))
                    * ((gA.1)⁻¹ * gB.1) from by ac_rfl,
                hcc, one_mul]
          _ = (gA⁻¹ * gB).1 := by
              rw [Subgroup.coe_mul, Subgroup.coe_inv]
      have hmem := mem_Ksub_of_kappa_fx fr (gA⁻¹ * gB) hκ
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at hmem
      exact hmem
    by_contra hne
    exact (coset_sep_KW hS fr h₁ h₂ (hwAQ i ⟨hi, hile⟩)
        (hwBQ (orderOf fr.ζ - i) ⟨hj1, hjm⟩) hne (hxAQ i ⟨hi, hile⟩)
        (hxBQ (orderOf fr.ζ - i) ⟨hj1, hjm⟩) hEAi
        (hB (orderOf fr.ζ - i) hj1 hjm)) hKsub
  -- ## 8.  the two linear equations of §2 (20)
  have hm2 : 2 ≤ orderOf fr.ζ := by
    have hne : orderOf fr.ζ ≠ 1 := fun h => fr.ζ_ne_one (orderOf_eq_one_iff.mp h)
    have hpos := orderOf_pos fr.ζ
    omega
  have hord : β ^ orderOf fr.ζ = 1 := beta_pow_m_eq_one hS fr h₁ hf₁ hβ hβα
  have hum1 : uSeq β (orderOf fr.ζ - 1) = fval α := uSeq_ord_sub_one hβ hβα hα0 hm2 hord
  have hl1 : fval (lam 1) = 1 := by
    rw [hlam 1 le_rfl (by omega)]
    exact wSeq_one hβα hα0
  have hlm1 : fval (lam (orderOf fr.ζ - 1)) = 1 := by
    rw [hlam (orderOf fr.ζ - 1) (by omega) (by omega)]
    exact wSeq_ord_sub_one hβα hα0 hm2 hord
  have h1m : 1 ≤ orderOf fr.ζ - 1 := by omega
  have hX1ne : fval X₁ ≠ 0 := by
    simp only [fval]; exact Units.ne_zero (X₁ : (E n)ˣ)
  have hY2ne : fval Y₂ ≠ 0 := by
    simp only [fval]; exact Units.ne_zero (Y₂ : (E n)ˣ)
  have hsne : (fval (nmF fr (kapFX fr hkK)))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    simp only [fval]; exact Units.ne_zero ((nmF fr (kapFX fr hkK)) : (E n)ˣ)
  -- `(*-1)`: `α + x₁⁻¹ = x₁ + s (x₂+α)⁻¹`
  have hE1 : fval α + (fval X₁)⁻¹
      = fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval Y₂ + fval α)⁻¹ := by
    have h := congrArg (fun z : ↥Q => (z : G)) (hcoset 1 le_rfl h1m)
    rw [hwAcoe 1 ⟨le_rfl, h1m⟩, hwBcoe (orderOf fr.ζ - 1) ⟨h1m, le_rfl⟩] at h
    have ha : vSeq (fval α) β 1 + (fval (lam 1))⁻¹ * (fval (UA 1))⁻¹
        = fval α + (fval X₁)⁻¹ := by
      rw [vSeq_one, hl1, hUAf 1 ⟨le_rfl, h1m⟩, uSeq_one, add_zero, inv_one, one_mul]
    have hb : fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹
          * (fval (UB (orderOf fr.ζ - 1)))⁻¹
        = fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval Y₂ + fval α)⁻¹ := by
      rw [hUBf (orderOf fr.ζ - 1) ⟨h1m, le_rfl⟩, hum1]
    rw [ha, hb] at h
    exact fr.zc_inj _ _ (by rw [map_add, α.2, map_inv₀, X₁.2])
      (by rw [map_add, X₁.2, map_mul, map_inv₀, (nmF fr (kapFX fr hkK)).2, map_inv₀,
        map_add, Y₂.2, α.2]) h
  -- `(**-1)`: `(x₁+α)⁻¹ = x₁ + s x₂⁻¹`
  have hE2 : (fval X₁ + fval α)⁻¹
      = fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval Y₂)⁻¹ := by
    have h := congrArg (fun z : ↥Q => (z : G)) (hcoset (orderOf fr.ζ - 1) h1m le_rfl)
    rw [show orderOf fr.ζ - (orderOf fr.ζ - 1) = 1 from by omega] at h
    rw [hwAcoe (orderOf fr.ζ - 1) ⟨h1m, le_rfl⟩, hwBcoe 1 ⟨le_rfl, h1m⟩] at h
    have ha : vSeq (fval α) β (orderOf fr.ζ - 1)
          + (fval (lam (orderOf fr.ζ - 1)))⁻¹ * (fval (UA (orderOf fr.ζ - 1)))⁻¹
        = (fval X₁ + fval α)⁻¹ := by
      rw [vSeq, hUAf (orderOf fr.ζ - 1) ⟨h1m, le_rfl⟩, hum1, hlm1]
      simp only [inv_one, one_mul]
      rw [CharTwo.add_self_eq_zero, zero_add]
    have hb : fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB 1))⁻¹
        = fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval Y₂)⁻¹ := by
      rw [hUBf 1 ⟨le_rfl, h1m⟩, uSeq_one, add_zero]
    rw [ha, hb] at h
    exact fr.zc_inj _ _ (by rw [map_inv₀, map_add, X₁.2, α.2])
      (by rw [map_add, X₁.2, map_mul, map_inv₀, (nmF fr (kapFX fr hkK)).2, map_inv₀,
        Y₂.2]) h
  have hBne : fval Y₂ + fval α ≠ 0 := by
    have hh := hUB (orderOf fr.ζ - 1) h1m le_rfl
    rwa [hum1] at hh
  have hAα : fval X₁ + fval α ≠ 0 := by
    have hh := hUA (orderOf fr.ζ - 1) h1m le_rfl
    rwa [hum1] at hh
  have hBα : fval Y₂ + fval α + fval α ≠ 0 := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    exact hY2ne
  have hE2' : (fval X₁ + fval α)⁻¹
      = fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval Y₂ + fval α + fval α)⁻¹ := by
    rw [show fval Y₂ + fval α + fval α = fval Y₂ from by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]]
    exact hE2
  have hdisc : fval X₁ * fval X₁ + fval α * fval X₁ + 1 ≠ 0 :=
    shift_disc_ne_zero hX1ne hBne hsne hE1
  obtain ⟨hbase, hBI⟩ := shift_solvable (α0 := fval α) (A := fval X₁)
    (B := fval Y₂ + fval α) (s := (fval (nmF fr (kapFX fr hkK)))⁻¹)
    hα0 hX1ne hBne hAα hBα hdisc (by rw [div_eq_mul_inv]; exact hE1)
    (by rw [div_eq_mul_inv]; exact hE2')
  have hY2eq : fval Y₂ = fval X₁ + fval α := by
    rw [← hbase, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  -- ## 9.  the family-B coordinate identity `x_i = w_i + α`
  have hcoord : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UB i))⁻¹
        = (fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB i))⁻¹) + fval α := by
    intro i hi hile
    have hlin : (fval (lam i))⁻¹ = uSeq β i * uSeq β i + fval α * uSeq β i + 1 := by
      rw [hlam i hi hile, ← uSeq_sq_add_mul hβ hβα hα0 hi (hN i hi hile)]
    rw [vSeq, hUBf i ⟨hi, hile⟩]
    exact vSeq_shift_coord hY2eq hBI hlin (hsideB i hi hile)
  have hwBQv : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1),
      wB i = zcQ fr (fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB i))⁻¹)
        (hsB i h.1 h.2) := by
    intro i h
    rw [hwBdef]; simp only [dif_pos h]
  have hxBQv : ∀ i (h : 1 ≤ i ∧ i ≤ orderOf fr.ζ - 1),
      xB i = zcQ fr (vSeq (fval α) β i + (fval (lam i))⁻¹ * (fval (UB i))⁻¹)
        (hsB' i h.1 h.2) := by
    intro i h
    rw [hxBdef]; simp only [dif_pos h]
  have hzcQFx : zcQF fr x = zcQ fr (fval x) x.2 := rfl
  have hzcQF1 : zcQF fr X₁ = zcQ fr (fval X₁) X₁.2 := rfl
  -- ## 10.  the witness of §2 (8) for the arbitrary `x`
  obtain ⟨d, y, hy, hxrel⟩ := cntSet_of_orbE hS fr (ω := ω₁) (ω' := ω₂) (x := zcQF fr x) hx
  obtain ⟨j, hjlt, f, hfd⟩ := exists_kapFX_zeta_coset hS fr d
  have hy_eq : y = zcQ fr (fval x + fval α) (by rw [map_add, x.2, α.2]) := by
    by_cases hj0 : j = 0
    · -- `j = 0`: the witness is in `K`, so `x = X₁` and `y = zcQF Y₂`
      have hdK : (d : G) ∈ Ksub H t :=
        (fr.mem_K_iff d).mpr (by rw [hfd, hj0, pow_zero, one_mul]; exact f.2)
      have hkK' : (k : G)⁻¹ * (d : G) ∈ Ksub H t :=
        (Ksub H t).mul_mem ((Ksub H t).inv_mem hkK) hdK
      have hxX1 : zcQF fr X₁ = zcQF fr x := by
        by_contra hne
        exact (coset_sep_KW hS fr h₁ h₂ (hzQ X₁) (hzQ x) hne (hzQ Y₂) hy hψ' hxrel) hkK'
      have hfvalx : fval x = fval X₁ := by
        refine zcQ_inj' fr x.2 X₁.2 ?_
        rw [← hzcQFx, ← hzcQF1]
        exact hxX1.symm
      have hyY2 : zcQF fr Y₂ = y := by
        have h2 : fcan hS.split (ω₁ * zcQF fr X₁) =
            qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ (ω₂ * y) := by
          rw [hxX1]; exact hxrel
        exact (witness_unique hS fr h₂ (hzQ X₁) (hzQ Y₂) hy hψ' h2).2
      have hG : (y : G) = fr.zc (fval x + fval α) := by
        rw [← hyY2, zcQF_coe]
        exact congrArg fr.zc (by rw [hY2eq, hfvalx])
      exact Subtype.ext (by rw [hG, zcQ_coe])
    · -- `1 ≤ j`: compare with the family-B one-step element at `j`
      have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hjm : j ≤ orderOf fr.ζ - 1 := by omega
      have hfdU : (fr.κ d : (E n)ˣ) = (fr.κ fr.ζ) ^ j * f.1 := by
        refine Units.ext ?_
        rw [Units.val_mul, Units.val_pow_eq_pow_val]
        exact hfd
      have hKsubB : (d : G)⁻¹ *
          ((dSeq hS fr lam j * kElF fr (tau hS fr (UB j)) ^ 2 * k : fr.KW) : G)
            ∈ Ksub H t := by
        obtain ⟨gB, hgB⟩ := hBcoset j hj1 hjm
        have hκ : (fr.κ (d⁻¹ * (dSeq hS fr lam j * kElF fr (tau hS fr (UB j)) ^ 2 * k)
              : fr.KW) : (E n)ˣ) = ((f⁻¹ * gB : ↥(FX n)) : (E n)ˣ) := by
          rw [map_mul, map_inv, hfdU, hgB, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
          rw [show (f.1)⁻¹ * ((fr.κ fr.ζ) ^ j)⁻¹ * ((fr.κ fr.ζ) ^ j * gB.1)
              = (f.1)⁻¹ * (((fr.κ fr.ζ) ^ j)⁻¹ * (fr.κ fr.ζ) ^ j) * gB.1 from by ac_rfl,
            inv_mul_cancel, mul_one]
        have hmem := mem_Ksub_of_kappa_fx fr (f⁻¹ * gB) hκ
        rw [Subgroup.coe_mul, Subgroup.coe_inv] at hmem
        exact hmem
      have hxwB : zcQF fr x = wB j := by
        by_contra hne
        exact (coset_sep_KW hS fr h₁ h₂ (hzQ x) (hwBQ j ⟨hj1, hjm⟩) hne hy
          (hxBQ j ⟨hj1, hjm⟩) hxrel (hB j hj1 hjm)) hKsubB
      have hfval_x : fval x
          = fval X₁ + (fval (nmF fr (kapFX fr hkK)))⁻¹ * (fval (UB j))⁻¹ := by
        have hxwB' : zcQ fr (fval x) x.2 = wB j := by
          have h := hxwB
          rw [hzcQFx] at h
          exact h
        refine zcQ_inj' fr x.2 (hsB j hj1 hjm) ?_
        rw [hxwB']
        exact hwBQv j ⟨hj1, hjm⟩
      have hxy : y = xB j := by
        have h2 : fcan hS.split (ω₁ * wB j) =
            qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ (ω₂ * y) := by
          rw [← hxwB]; exact hxrel
        exact (witness_unique hS fr h₂ (hwBQ j ⟨hj1, hjm⟩) (hxBQ j ⟨hj1, hjm⟩) hy
          (hB j hj1 hjm) h2).2.symm
      have hG : (y : G) = fr.zc (fval x + fval α) := by
        rw [hxy, hxBcoe j ⟨hj1, hjm⟩]
        exact congrArg fr.zc (by
          rw [hcoord j hj1 hjm, ← hfval_x])
      exact Subtype.ext (by rw [hG, zcQ_coe])
  refine ⟨d, ?_⟩
  rw [hxrel]
  exact congrArg (fun z => qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ (ω₂ * z)) hy_eq

end Work.PSU3.StageB.Omega
