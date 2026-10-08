/-
# `Work.PSU3.StageB.ThetaMain` — Peterfalvi II, Ch. VII §3: the assembly of `θ = 1`

This module assembles the pieces of Peterfalvi's computation of `nm` and `ω²`
(Ch. VII §3, pp. 275–277) into the functional equation of step (3) and the final
root-counting argument:

* `cE fr = κ ζ + (κ ζ)⁻¹` and `xE fr hω = \bar ω` (the `c` and `x` of §3);
* the fixed units `F* = FX n` (`|F*| = 2ⁿ - 1`), the action `nm` on them (`nmF`, `nmEquiv`),
  and the exceptional element `exc` (Peterfalvi's `α^{-τ}`);
* **§3 (3)**: for every `u ∈ F*`, `u ≠ exc`, the functional equation
  `(c + c⁻¹ + (ā⁻¹)²)^μ = α² + ((ā⁻¹)²)^μ` with `ā = fval u`, where `nm a = a^μ`;
* the Finset `S` of the `2ⁿ - 2` admissible values `ā⁻²`, and the final application of
  `ThetaEnd`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.GaloisField.fixedField_card
import Submission.Work.PSU3.StageB.Theta
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.nm_pow_map
import Submission.Work.PSU3.StageB.nm_injective_on_fixed
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.ThetaOmega
import Submission.Work.PSU3.StageB.ThetaEnd
import Submission.Work.PSU3.StageB.theta_law
import Submission.Work.PSU3.StageB.theta_bar_mul
import Submission.Work.PSU3.StageB.omega_inv_mul_sconjInv
import Submission.Work.PSU3.StageB.fixedUnits_card
import Submission.Work.PSU3.StageB.nm_pow_map_reduced
import Submission.Work.PSU3.StageB.fe_alg

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.ThmF
open Work.PSU3
open Classical

namespace Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## The number of fixed units -/

/-- `|F*| = 2ⁿ - 1`. -/
theorem card_FX (n : ℕ) (hn : 1 ≤ n) : Nat.card ↥(FX n) = 2 ^ n - 1 := by
  rw [← fixedUnits_card n hn]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => Iff.rfl)

section Frame

variable (fr : CoarseFrame H Q t n)

/-! ## The field elements `ζ = κ ζ`, `c = ζ + ζ⁻¹` and `x = \bar ω` -/

/-- `ζ = κ ζ ∈ E n`, the scalar of Peterfalvi Ch. VII §3 (2). -/
noncomputable def zetaE : E n := ((fr.κ fr.ζ : (E n)ˣ) : E n)

theorem zetaE_ne_zero : zetaE fr ≠ 0 := by
  rw [zetaE]
  exact Units.ne_zero _

/-- `c = ζ + ζ⁻¹ ∈ E n`, the `c` of the functional equation of Ch. VII §3 (3). -/
noncomputable def cE : E n := ((fr.κ fr.ζ : (E n)ˣ) : E n) + (((fr.κ fr.ζ : (E n)ˣ) : E n))⁻¹

/-- `c` is fixed by `σE`: `σ(κζ) = (κζ)⁻¹` and `c = κζ + (κζ)⁻¹`. -/
theorem cE_fixed : σE (cE fr) = cE fr := by
  rw [cE, map_add, map_inv₀, eq_inv_of_mul_eq_one_right fr.ζ_norm, inv_inv, add_comm]

/-- `c ≠ 0`. -/
theorem cE_ne_zero : cE fr ≠ 0 := by
  rw [cE]
  intro h
  have hκζ_ne : (fr.κ fr.ζ : (E n)ˣ) ≠ 1 := fun h1 =>
    fr.ζ_ne_one (fr.κ_injective (by rw [h1, map_one]))
  have hxz : (((fr.κ fr.ζ : (E n)ˣ) : E n)) ≠ 0 := Units.ne_zero _
  have h1 : (((fr.κ fr.ζ : (E n)ˣ) : E n)) = (((fr.κ fr.ζ : (E n)ˣ) : E n))⁻¹ := by
    have hh := add_eq_zero_iff_eq_neg.mp h
    rwa [CharTwo.neg_eq] at hh
  have h2 : (((fr.κ fr.ζ : (E n)ˣ) : E n)) * (((fr.κ fr.ζ : (E n)ˣ) : E n)) = 1 := by
    have hh : (((fr.κ fr.ζ : (E n)ˣ) : E n)) * (((fr.κ fr.ζ : (E n)ˣ) : E n))
        = (((fr.κ fr.ζ : (E n)ˣ) : E n))⁻¹ * (((fr.κ fr.ζ : (E n)ˣ) : E n)) :=
      congrArg (fun x => x * (((fr.κ fr.ζ : (E n)ˣ) : E n))) h1
    rw [hh, inv_mul_cancel₀ hxz]
  have h3 : (((fr.κ fr.ζ : (E n)ˣ) : E n)) = 1 :=
    sq_eq_sq_char2 (by simpa [pow_two] using h2)
  exact hκζ_ne (Units.ext h3)

/-- `x = \bar ω ∈ E n`. -/
noncomputable def xE {ω : G} (hω : OmegaHyp fr ω) : E n :=
  Multiplicative.toAdd (fr.bar (omQ fr hω))

/-- `\bar ω ≠ 0`, since `ω ∉ Q₀`. -/
theorem xE_ne_zero {ω : G} (hω : OmegaHyp fr ω) : xE fr hω ≠ 0 := by
  intro hc
  have hbar : fr.bar (omQ fr hω) = 1 := by
    have h := congrArg Multiplicative.ofAdd hc
    simpa [xE] using h
  exact hω.2.1 (by rw [← omQ_coe fr hω]; exact (fr.bar_eq_one_iff (omQ fr hω)).mp hbar)

/-! ## The exceptional element of `F*` -/

/-- The element of `F*` whose field element is `α⁻¹`. -/
noncomputable def alphaInvFX {ω : G} (hω : OmegaHyp fr ω) : ↥(FX n) :=
  mkFX ((alpha fr hω)⁻¹) (by rw [map_inv₀, alpha_fixed fr hω])
    (inv_ne_zero (alpha_ne_zero fr hω))

theorem fval_alphaInvFX {ω : G} (hω : OmegaHyp fr ω) :
    fval (alphaInvFX fr hω) = (alpha fr hω)⁻¹ :=
  fval_mkFX _ _ _

/-- The exceptional element of `F*`: the unique `u` with `nm u = α⁻¹`, for which the
substitution of Ch. VII §3 (3) degenerates (`α + nm(ā)⁻¹ = 0`). -/
noncomputable def exc (hS : PSU3Hyp H Q t) {ω : G} (hω : OmegaHyp fr ω) : ↥(FX n) :=
  tau hS fr (alphaInvFX fr hω)

theorem nmF_exc (hS : PSU3Hyp H Q t) {ω : G} (hω : OmegaHyp fr ω) :
    nmF fr (exc fr hS hω) = alphaInvFX fr hω :=
  nm_tau hS fr (alphaInvFX fr hω)

/-- `(nm (κ w) : E n) = fval (nmF fr w)` for the `KW`-element `κ w = kElF fr w`. -/
theorem nm_kappa_kElF (w : ↥(FX n)) :
    ((fr.nm (fr.κ (kElF fr w)) : (E n)ˣ) : E n) = fval (nmF fr w) := by
  rw [kElF_kappa]
  rfl

/-! ## The canonical data of `ω` -/

/-- The three consequences of `ThetaOmega` that Ch. VII §3 uses. -/
theorem omega_data (hS : PSU3Hyp H Q t) {ω : G} (hω : OmegaHyp fr ω) :
    (fcan hS.split (omQ fr hω) : G) = (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) ∧
    ((hcan hS.split (omQ fr hω) : G) ∈ W H t) ∧
    (hcan hS.split ((omQ fr hω)⁻¹) : G) = (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ := by
  obtain ⟨g, hg, hh, hhW, heq⟩ := hω.2.2
  obtain ⟨h1, h2, h3, h4⟩ := ThetaOmega fr hS.split hω hg hhW heq
  exact ⟨h3, by rw [h2]; exact hhW, h4⟩

end Frame

/-! ## The characteristic-two lemma behind the exponent step -/

/-- In characteristic two `X^{2μ} = (X^μ)²`, so `bb² = c + c⁻¹ + (a⁻¹)²` together with
`bb^μ = α + (a^μ)⁻¹` gives `(c + c⁻¹ + (a⁻¹)²)^μ = α² + ((a⁻¹)²)^μ`. -/
theorem fe_pow {F : Type*} [Field F] [CharP F 2] {c a α bb : F} {μ : ℕ}
    (hA : bb ^ 2 = c + c⁻¹ + (a⁻¹) ^ 2)
    (hb : bb ^ μ = α + (a ^ μ)⁻¹) :
    (c + c⁻¹ + (a⁻¹) ^ 2) ^ μ = α ^ 2 + ((a⁻¹) ^ 2) ^ μ := by
  rw [← hA, ← pow_mul, Nat.mul_comm, pow_mul, hb, CharTwo.add_sq]
  congr 1
  calc ((a ^ μ)⁻¹) ^ 2 = (a ^ (μ * 2))⁻¹ := by rw [inv_pow, ← pow_mul]
    _ = (a ^ (2 * μ))⁻¹ := by rw [Nat.mul_comm μ 2]
    _ = (a⁻¹) ^ (2 * μ) := by rw [inv_pow]
    _ = ((a⁻¹) ^ 2) ^ μ := by rw [pow_mul]

/-! ## Peterfalvi II, Ch. VII §3 (3): the functional equation -/

section FE

variable (fr : CoarseFrame H Q t n) (hS : PSU3Hyp H Q t)

theorem theta_FE {ω : G} (hω : OmegaHyp fr ω)
    {μ : ℕ} (hμ : ∀ a : (E n)ˣ, σE (a : E n) = a → fr.nm a = a ^ μ)
    {u : ↥(FX n)} (hu : u ≠ exc fr hS hω) :
    (cE fr + (fval u)⁻¹ ^ 2) ^ μ
      = (alpha fr hω) ^ 2 + ((fval u)⁻¹ ^ 2) ^ μ := by
  obtain ⟨hfω, hW, hzinv⟩ := omega_data fr hS hω
  have hc0 : zetaE fr ≠ 0 := zetaE_ne_zero fr
  have hā : fval u ≠ 0 := Units.ne_zero _
  have hx0 : xE fr hω ≠ 0 := xE_ne_zero fr hω
  -- `nm` on `F*` is the power map `a ↦ a^μ`
  have hfval_u : fval (nmF fr u) = (fval u) ^ μ := by
    show ((nmF fr u : (E n)ˣ) : E n) = ((u : (E n)ˣ) : E n) ^ μ
    rw [nmF_coe, hμ u.1 u.2, Units.val_pow_eq_pow_val]
  -- the substitution is nondegenerate away from the exceptional element
  have hy0 : alpha fr hω + (fval (nmF fr u))⁻¹ ≠ 0 := by
    intro hc
    have h1 : (fval (nmF fr u))⁻¹ = alpha fr hω :=
      CharTwo.add_eq_zero.mp (by rw [add_comm]; exact hc)
    have h2 : fval (nmF fr u) = (alpha fr hω)⁻¹ := by rw [← h1, inv_inv]
    have h3 : u = exc fr hS hω := by
      apply nmF_injective hS fr
      rw [nmF_exc fr hS hω]
      apply Subtype.ext
      apply Units.ext
      exact h2.trans (fval_alphaInvFX fr hω).symm
    exact hu h3
  -- `y`: the element of `F*` with `fval y = α + (nm u)⁻¹`
  let y : ↥(FX n) := mkFX (alpha fr hω + (fval (nmF fr u))⁻¹)
    (by rw [map_add, map_inv₀, alpha_fixed fr hω, (nmF fr u).2]) hy0
  have hyval : fval y = alpha fr hω + (fval (nmF fr u))⁻¹ := rfl
  -- the two elements of `KW`: `a` with `κ a = u`, and `b` with `nm (κ b) = fval y`
  let a : fr.KW := kElF fr u
  let b : fr.KW := kElF fr (tau hS fr y)
  have ha : (a : G) ∈ Ksub H t := kElF_mem_Ksub fr u
  have hb : (b : G) ∈ Ksub H t := kElF_mem_Ksub fr (tau hS fr y)
  have hκa : ((fr.κ a : (E n)ˣ) : E n) = fval u := by
    show ((fr.κ (kElF fr u) : (E n)ˣ) : E n) = fval u
    rw [kElF_kappa]
  have hκb : ((fr.κ b : (E n)ˣ) : E n) = fval (tau hS fr y) := by
    show ((fr.κ (kElF fr (tau hS fr y)) : (E n)ˣ) : E n) = fval (tau hS fr y)
    rw [kElF_kappa]
  have hnm_a : ((fr.nm (fr.κ a) : (E n)ˣ) : E n) = fval (nmF fr u) := by
    show ((fr.nm (fr.κ (kElF fr u)) : (E n)ˣ) : E n) = fval (nmF fr u)
    rw [nm_kappa_kElF]
  have hnm_b : ((fr.nm (fr.κ b) : (E n)ˣ) : E n) = alpha fr hω + (fval (nmF fr u))⁻¹ := by
    show ((fr.nm (fr.κ (kElF fr (tau hS fr y))) : (E n)ˣ) : E n) = _
    rw [nm_kappa_kElF, nm_tau, hyval]
  -- the two `fcan`-arguments coincide
  have harg : (omQ fr hω)⁻¹ * sconjInv fr a ha = omQ fr hω * sconj fr b hb := by
    apply Subtype.ext
    rw [omega_inv_mul_sconjInv fr hω a ha, Subgroup.coe_mul, omQ_coe,
      sconj_eq_zc fr hS.split b hb]
    rw [hnm_a, hnm_b]
  -- Peterfalvi §3 (2) at `a` and at `b`, and H6 at `a`
  have hbara : (1 + zetaE fr * (fval u) ^ 2) *
      Multiplicative.toAdd (fr.bar (fcan hS.split (omQ fr hω * sconj fr a ha)))
      = zetaE fr * xE fr hω := by
    have h := theta_bar_mul fr hS.split hω hW hfω hzinv a ha
    rw [hκa] at h
    exact h
  have hbarb : (1 + zetaE fr * (fval (tau hS fr y)) ^ 2) *
      Multiplicative.toAdd (fr.bar (fcan hS.split (omQ fr hω * sconj fr b hb)))
      = zetaE fr * xE fr hω := by
    have h := theta_bar_mul fr hS.split hω hW hfω hzinv b hb
    rw [hκb] at h
    exact h
  have hlaw : Multiplicative.toAdd (fr.bar (fcan hS.split (omQ fr hω * sconj fr a ha)))
      = (fval u)⁻¹ ^ 2 * zetaE fr *
        Multiplicative.toAdd (fr.bar (fcan hS.split (omQ fr hω * sconj fr b hb))) := by
    have h := theta_law fr hS.split hω hfω a ha
    rw [hκa] at h
    rw [harg] at h
    exact h
  have hAb := fe_alg (c := zetaE fr) (ā := fval u)
    (Ab := (fval (tau hS fr y)) ^ 2)
    (Ua := Multiplicative.toAdd (fr.bar (fcan hS.split (omQ fr hω * sconj fr a ha))))
    (Ub := Multiplicative.toAdd (fr.bar (fcan hS.split (omQ fr hω * sconj fr b hb))))
    (x := xE fr hω) hc0 hā hx0 hbara hbarb hlaw
  -- `bb = fval (τ y)` is the `bb` of the exponent step
  have hbpow : (fval (tau hS fr y)) ^ μ = alpha fr hω + ((fval u) ^ μ)⁻¹ := by
    have h1 : fval (nmF fr (tau hS fr y)) = (fval (tau hS fr y)) ^ μ := by
      show ((nmF fr (tau hS fr y) : (E n)ˣ) : E n) = _
      rw [nmF_coe, hμ (tau hS fr y).1 (tau hS fr y).2, Units.val_pow_eq_pow_val]
    rw [← h1, nm_tau, hyval, hfval_u]
  have hfin := fe_pow (c := zetaE fr) (a := fval u) (α := alpha fr hω)
    (bb := fval (tau hS fr y)) hAb hbpow
  rwa [show zetaE fr + (zetaE fr)⁻¹ = cE fr from rfl] at hfin

end FE

/-! ## The main theorem -/

section Main

variable (fr : CoarseFrame H Q t n)

theorem theta_trivial_frame (hS : PSU3Hyp H Q t) {ω : G} (hω : OmegaHyp fr ω) :
    ∃ i : ℕ,
      (∀ a : (E n)ˣ, σE (a : E n) = a → fr.nm a = a ^ (2 ^ (i + 1))) ∧
      ω ^ 2 = fr.zc ((cE fr) ^ (2 ^ i)) := by
  classical
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · -- `n = 0`: no such frame exists
      have hσ : ∀ x : E 0, σE x = x := fun x => by
        show x ^ (2 ^ 0) = x
        simp
      have hz : (fr.κ fr.ζ : E 0) * (fr.κ fr.ζ : E 0) = 1 := by
        have h := fr.ζ_norm
        rwa [hσ] at h
      have h1 : ((fr.κ fr.ζ : (E 0)ˣ) : E 0) = 1 := by
        have h2 : (((fr.κ fr.ζ : (E 0)ˣ) : E 0)) ^ 2 = (1 : E 0) ^ 2 := by
          rw [one_pow, pow_two]
          exact hz
        exact sq_eq_sq_char2 h2
      exact absurd (fr.κ_injective (Units.ext (by simpa using h1))) fr.ζ_ne_one
    · -- `n = 1`: `F* = 1` is trivial and `κζ + (κζ)⁻¹ = 1`
      have hcard1 : Nat.card ↥(FX 1) = 1 := by
        rw [card_FX 1 le_rfl]
        norm_num
      haveI : Subsingleton ↥(FX 1) := (Nat.card_eq_one_iff_unique.mp hcard1).1
      have hnfix : σE (alpha fr hω) = alpha fr hω := alpha_fixed fr hω
      have hα0 : alpha fr hω ≠ 0 := alpha_ne_zero fr hω
      have hcfix : σE (cE fr) = cE fr := cE_fixed fr
      have hc0 : cE fr ≠ 0 := cE_ne_zero fr
      have h2 : alpha fr hω = cE fr := by
        have h1 : (mkFX (alpha fr hω) hnfix hα0 : ↥(FX 1)) = mkFX (cE fr) hcfix hc0 :=
          Subsingleton.elim _ _
        have h3 := congrArg (fun u : ↥(FX 1) => fval u) h1
        rwa [fval_mkFX, fval_mkFX] at h3
      refine ⟨0, ?_, ?_⟩
      · intro a ha
        have hmem : (⟨a, ha⟩ : ↥(FX 1)) = 1 := Subsingleton.elim _ _
        have ha1 : a = 1 := by
          have h := congrArg (fun u : ↥(FX 1) => ((u : (E 1)ˣ))) hmem
          simpa using h
        rw [ha1]
        simp
      · rw [show (2 : ℕ) ^ 0 = 1 from by norm_num, pow_one, ← h2, alpha_spec, pow_two]
  · -- the main case `n ≥ 2`
    haveI : Fintype ↥(FX n) := Fintype.ofFinite _
    obtain ⟨μ, hμpos, hμle, hμ⟩ :=
      nm_pow_map_reduced hS fr (card_FX n (by omega)) hn
    have hcard : Nat.card {a : (E n)ˣ // σE (a : E n) = a} = 2 ^ n - 1 :=
      fixedUnits_card n (by omega)
    obtain ⟨i, hi, hω2⟩ := ThetaEnd fr hω hμ hμpos hμle hcard
      ((Finset.univ.erase (exc fr hS hω)).image (fun u : ↥(FX n) => (fval u)⁻¹ ^ 2))
      (by
        intro A hA
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hA
        rw [map_pow, map_inv₀, u.2])
      (by
        have hinj : Function.Injective (fun u : ↥(FX n) => (fval u)⁻¹ ^ 2) := by
          intro u v huv
          have h2 : (fval u) ^ 2 = (fval v) ^ 2 := by
            have h : (fval u)⁻¹ ^ 2 = (fval v)⁻¹ ^ 2 := huv
            rw [inv_pow, inv_pow] at h
            exact inv_injective h
          exact Subtype.ext (Units.ext (sq_eq_sq_char2 h2))
        have hcard' : Fintype.card ↥(FX n) = 2 ^ n - 1 := by
          rw [← Nat.card_eq_fintype_card]
          exact card_FX n (by omega)
        rw [Finset.card_image_of_injective _ hinj,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard']
        omega)
      (by
        intro A hA
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hA
        have hue : u ≠ exc fr hS hω := (Finset.mem_erase.mp hu).1
        exact theta_FE fr hS hω hμ hue)
    exact ⟨i, hi, hω2⟩

end Main

end Work.PSU3.StageB
