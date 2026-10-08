/-
# `Work.PSU3.StageB.Omega.API` — the frame API for Peterfalvi Ch. VII §2

Groundwork for the proof of `Work.PSU3.StageB.exists_omega_of_fpf` (Peterfalvi II, Ch. VII
§2, pp. 268–275).  Everything here is stated for an abstract `CoarseFrame` `fr` in the
hypotheses of `PSU3Hyp H Q t`, together with the canonical maps `fcan, gcan, hcan` of
`Work.PSU3.StageB.Canon`.

Contents (numbers refer to Peterfalvi Ch. VII §2):

* `FX`, `fval`, `mkFX` — the fixed field `F*` of `σE` as a subgroup of `(E n)ˣ`;
* `nmF`, `nmFHom`, `nmEquiv`, `tau` — the action `nm` of `K` on `Q₀ ≅ F` on the fixed field,
  and its inverse `τ` (Peterfalvi's `τ` for `1 + θ`);
* `kElF`, `zcQF`, `sconjF` — the `KW ∩ Ksub`-element with `κ d = u`, and the elements
  `zc u`, `sᵈ` of `Q₀`;
* **(1)** `canon_zcQF`: for `u ∈ F*`, `f (zc u) = g (zc u) = zc u⁻¹` and
  `h (zc u) = (kElF (τ u))²`;
* **(W1)** `fcan_mem_Q0_iff`: `f (w) ∈ Q₀ ↔ w ∈ Q₀`;
* **(4)** `fcan_shift_Q0`: `f (ω x) = f (ω) y` with `ω ∉ Q₀`, `x, y ∈ Q₀` forces `x = 1`;
* **(2)** `fcan_mul_zcQF` and **(3)** `fcan_zcQF_mul`: the two recursions of §2;
* `t_conj_mem_D`, `conj_mem_Q0_of_mem_D` — `D` is `t`-stable and preserves `Q₀`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.GaloisField.fixedField_card
import Submission.Work.PSU3.StageB.Theta
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.StageB.nm_injective_on_fixed
import Submission.Work.PSU3.StageC.FSuz
import Submission.Work.ThmF.Setup

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
open Classical

namespace Work.PSU3.StageB

open Work.ThmF
open Work.PSU3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

noncomputable def zcQ (fr : CoarseFrame H Q t n) (v : E n) (hv : σE v = v) : Q :=
  Work.PSU3.StageC.zcQ fr v hv

@[simp] theorem zcQ_coe (fr : CoarseFrame H Q t n) (v : E n) (hv : σE v = v) :
    ((zcQ fr v hv : Q) : G) = fr.zc v := rfl

theorem zcQ_coe_ne_one (fr : CoarseFrame H Q t n) (v : E n) (hv : σE v = v) (hv0 : v ≠ 0) :
    ((zcQ fr v hv : Q) : G) ≠ 1 :=
  Work.PSU3.StageC.zcQ_coe_ne_one fr v hv hv0

/-! ## The fixed units `F*` -/

/-- The `σE`-fixed units of `E n`: `F*` for `F` the fixed field of `σE`. -/
noncomputable def FX (n : ℕ) : Subgroup (E n)ˣ where
  carrier := {u | σE (u : E n) = (u : E n)}
  mul_mem' := by
    intro a b ha hb
    show σE ((a * b : (E n)ˣ) : E n) = ((a * b : (E n)ˣ) : E n)
    rw [Units.val_mul, map_mul, ha, hb]
  one_mem' := by
    show σE ((1 : (E n)ˣ) : E n) = ((1 : (E n)ˣ) : E n)
    simp
  inv_mem' := by
    intro a ha
    show σE ((a⁻¹ : (E n)ˣ) : E n) = ((a⁻¹ : (E n)ˣ) : E n)
    rw [Units.val_inv_eq_inv_val, σE_inv, ha]

instance (n : ℕ) : Finite ↥(FX n) :=
  Finite.of_injective (fun u : ↥(FX n) => (u.1 : (E n)ˣ)) Subtype.val_injective

/-- The underlying field element of `u ∈ F*`. -/
abbrev fval {n : ℕ} (u : ↥(FX n)) : E n := ((u : (E n)ˣ) : E n)

@[simp] lemma fval_inv {n : ℕ} (u : ↥(FX n)) : fval u⁻¹ = (fval u)⁻¹ := by
  show (((u⁻¹ : ↥(FX n)) : (E n)ˣ) : E n) = _
  rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]

@[simp] lemma fval_mul {n : ℕ} (u v : ↥(FX n)) : fval (u * v) = fval u * fval v := by
  show (((u * v : ↥(FX n)) : (E n)ˣ) : E n) = _
  rw [Subgroup.coe_mul, Units.val_mul]

/-- `v ∈ F*` as an element of `FX n`. -/
noncomputable def mkFX (v : E n) (hv : σE v = v) (hv0 : v ≠ 0) : ↥(FX n) :=
  ⟨Units.mk0 v hv0, hv⟩

@[simp] lemma fval_mkFX (v : E n) (hv : σE v = v) (hv0 : v ≠ 0) :
    fval (mkFX v hv hv0) = v := rfl

/-- `f` of the identity is the identity. -/
lemma fcan_apply_one (h : IsSplitRankOne H Q t) : fcan h (1 : Q) = 1 := by
  unfold fcan
  exact dif_pos (Subgroup.coe_one Q)

/-- `nm` restricted to the fixed units. -/
noncomputable def nmF (fr : CoarseFrame H Q t n) (u : ↥(FX n)) : ↥(FX n) :=
  ⟨fr.nm u.1, fr.nm_F u.1 u.2⟩

@[simp] lemma nmF_coe (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((nmF fr u : ↥(FX n)) : (E n)ˣ) = fr.nm u.1 := rfl

@[simp] lemma nmF_one (fr : CoarseFrame H Q t n) : nmF fr 1 = 1 := by
  apply Subtype.ext
  rw [nmF_coe]
  show fr.nm ((1 : ↥(FX n)) : (E n)ˣ) = (1 : (E n)ˣ)
  rw [Subgroup.coe_one, map_one]

@[simp] lemma nmF_mul (fr : CoarseFrame H Q t n) (u v : ↥(FX n)) :
    nmF fr (u * v) = nmF fr u * nmF fr v := by
  apply Subtype.ext
  simp only [nmF_coe, Subgroup.coe_mul]
  exact map_mul fr.nm u.1 v.1

/-- `nm` as a monoid homomorphism of `F*`. -/
noncomputable def nmFHom (fr : CoarseFrame H Q t n) : ↥(FX n) →* ↥(FX n) where
  toFun := nmF fr
  map_one' := nmF_one fr
  map_mul' := nmF_mul fr

@[simp] lemma nmF_inv (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    nmF fr u⁻¹ = (nmF fr u)⁻¹ :=
  map_inv (nmFHom fr) u

lemma nmF_injective (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) :
    Function.Injective (nmF fr) := by
  intro a b hab
  apply Subtype.ext
  have h1 : fr.nm a.1 = fr.nm b.1 := by
    rw [← nmF_coe, ← nmF_coe, hab]
  have h2 : fr.nm (a.1 * b.1⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 : σE ((a.1 * b.1⁻¹ : (E n)ˣ) : E n) = ((a.1 * b.1⁻¹ : (E n)ˣ) : E n) := by
    have h3a : ((a.1 * b.1⁻¹ : (E n)ˣ) : E n) = (a.1 : E n) * ((b.1 : E n))⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
    rw [h3a, map_mul, σE_inv, a.2, b.2]
  have h4 := nm_injective_on_fixed hS fr (a.1 * b.1⁻¹) h3 h2
  have h5 : a.1 * b.1⁻¹ = 1 := h4
  have h6 : a.1 = b.1 := by
    have hh := congrArg (fun z : (E n)ˣ => z * b.1) h5
    simpa using hh
  exact h6

/-- `nm` as an automorphism of `F*`. -/
noncomputable def nmEquiv (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) :
    ↥(FX n) ≃* ↥(FX n) :=
  MulEquiv.ofBijective (nmFHom fr)
    ⟨nmF_injective hS fr, (Finite.injective_iff_surjective).mp (nmF_injective hS fr)⟩

@[simp] lemma nmEquiv_apply (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    nmEquiv hS fr u = nmF fr u := rfl

/-- `τ`: the inverse of `nm` on `F*`. -/
noncomputable def tau (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) :
    ↥(FX n) →* ↥(FX n) :=
  (nmEquiv hS fr).symm.toMonoidHom

lemma tau_mul (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u v : ↥(FX n)) :
    tau hS fr (u * v) = tau hS fr u * tau hS fr v := map_mul _ _ _

@[simp] lemma tau_nm (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    tau hS fr (nmF fr u) = u := by
  show (nmEquiv hS fr).symm (nmEquiv hS fr u) = u
  exact (nmEquiv hS fr).symm_apply_apply u

@[simp] lemma nm_tau (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    nmF fr (tau hS fr u) = u := by
  show nmEquiv hS fr ((nmEquiv hS fr).symm u) = u
  exact (nmEquiv hS fr).apply_symm_apply u

/-! ## The `KW ∩ Ksub`-element attached to `u ∈ F*` -/

/-- The element of `KW ∩ Ksub` with `κ d = u`. -/
noncomputable def kElF (fr : CoarseFrame H Q t n) (u : ↥(FX n)) : fr.KW :=
  Classical.choose (fr.K_surj u.1 u.2)

lemma kElF_kappa (fr : CoarseFrame H Q t n) (u : ↥(FX n)) : fr.κ (kElF fr u) = u.1 :=
  Classical.choose_spec (fr.K_surj u.1 u.2)

lemma kElF_mem_Ksub (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((kElF fr u : fr.KW) : G) ∈ Ksub H t :=
  (fr.mem_K_iff _).mpr (by rw [kElF_kappa]; exact u.2)

@[simp] lemma kElF_mul (fr : CoarseFrame H Q t n) (u v : ↥(FX n)) :
    kElF fr (u * v) = kElF fr u * kElF fr v := by
  apply fr.κ_injective
  rw [map_mul, kElF_kappa, kElF_kappa, kElF_kappa, Subgroup.coe_mul]

@[simp] lemma kElF_inv (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    kElF fr u⁻¹ = (kElF fr u)⁻¹ := by
  apply fr.κ_injective
  rw [map_inv, kElF_kappa, kElF_kappa, Subgroup.coe_inv]

/-! ## §2 (1): the canonical data of the elements of `Q₀` -/

/-- `zc u` as an element of `Q`, for `u ∈ F*`. -/
noncomputable def zcQF (fr : CoarseFrame H Q t n) (u : ↥(FX n)) : Q :=
  zcQ fr (fval u) u.2

@[simp] lemma zcQF_coe (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((zcQF fr u : Q) : G) = fr.zc (fval u) := rfl

/-- `s^d` (the conjugate of `s`) as an element of `Q`, for `d = kElF u`. -/
noncomputable def sconjF (fr : CoarseFrame H Q t n) (u : ↥(FX n)) : Q :=
  sconj fr (kElF fr u) (kElF_mem_Ksub fr u)

@[simp] lemma sconjF_coe (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    (sconjF fr u : G) = (kElF fr u : G)⁻¹ * frameS fr * (kElF fr u : G) := rfl

lemma sconjF_def (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    sconjF fr u = sconj fr (kElF fr u) (kElF_mem_Ksub fr u) := rfl

/-- `s^d = zc (nm u)` for `d = kElF u`. -/
theorem sconjF_eq_zcQF (fr : CoarseFrame H Q t n) (hS : PSU3Hyp H Q t) (u : ↥(FX n)) :
    sconjF fr u = zcQF fr (nmF fr u) := by
  apply Subtype.ext
  rw [sconjF_def, sconj_eq_zc fr hS.split (kElF fr u) (kElF_mem_Ksub fr u), kElF_kappa]
  rfl

/-- `s^{d⁻¹}` in the `sconjF` language. -/
lemma sconjInv_kElF (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    sconjInv fr (kElF fr u) (kElF_mem_Ksub fr u) = sconjF fr u⁻¹ := by
  apply Subtype.ext
  show (kElF fr u : G) * frameS fr * (kElF fr u : G)⁻¹ =
    (kElF fr u⁻¹ : G)⁻¹ * frameS fr * (kElF fr u⁻¹ : G)
  rw [kElF_inv, Subgroup.coe_inv, inv_inv]

/-- **(1)**, `G`-form.  For `u ∈ F*`: `f (zc u) = g (zc u) = zc u⁻¹` and
`h (zc u) = (kElF (τ u))²`. -/
theorem canon_zcQF_coe (fr : CoarseFrame H Q t n) (hS : PSU3Hyp H Q t) (u : ↥(FX n)) :
    ((fcan hS.split (zcQF fr u) : Q) : G) = fr.zc (fval u⁻¹) ∧
    ((gcan hS.split (zcQF fr u) : Q) : G) = fr.zc (fval u⁻¹) ∧
    (hcan hS.split (zcQF fr u) : G) =
      (kElF fr (tau hS fr u) : G) * (kElF fr (tau hS fr u) : G) := by
  have hd : ((kElF fr (tau hS fr u) : fr.KW) : G) ∈ Ksub H t :=
    kElF_mem_Ksub fr (tau hS fr u)
  have hsc := canon_sconj fr hS.split (kElF fr (tau hS fr u)) hd
  have hz1 : zcQF fr u = sconjF fr (tau hS fr u) := by
    rw [sconjF_eq_zcQF fr hS (tau hS fr u), nm_tau]
  have hz2 : ((fcan hS.split (sconjF fr (tau hS fr u)) : Q) : G) = fr.zc (fval u⁻¹) := by
    rw [sconjF_def, hsc.1, sconjInv_kElF, sconjF_eq_zcQF fr hS ((tau hS fr u))⁻¹, nmF_inv,
      nm_tau, zcQF_coe]
  have hz3 : ((gcan hS.split (sconjF fr (tau hS fr u)) : Q) : G) = fr.zc (fval u⁻¹) := by
    rw [sconjF_def, hsc.2.1, sconjInv_kElF, sconjF_eq_zcQF fr hS ((tau hS fr u))⁻¹, nmF_inv,
      nm_tau, zcQF_coe]
  refine ⟨?_, ?_, ?_⟩
  · rw [hz1, sconjF_def]; exact hz2
  · rw [hz1, sconjF_def]; exact hz3
  · rw [hz1, sconjF_def]
    exact hsc.2.2

/-- **(1)**, element form. -/
theorem canon_zcQF (fr : CoarseFrame H Q t n) (hS : PSU3Hyp H Q t) (u : ↥(FX n)) :
    fcan hS.split (zcQF fr u) = zcQF fr u⁻¹ ∧
    gcan hS.split (zcQF fr u) = zcQF fr u⁻¹ ∧
    (hcan hS.split (zcQF fr u) : G) =
      (kElF fr (tau hS fr u) : G) * (kElF fr (tau hS fr u) : G) := by
  obtain ⟨h1, h2, h3⟩ := canon_zcQF_coe fr hS u
  exact ⟨Subtype.ext (by rw [h1, zcQF_coe]), Subtype.ext (by rw [h2, zcQF_coe]), h3⟩

/-- `f (zc u) = zc u⁻¹` for `u ∈ F*`, coerced form. -/
theorem fcan_zcQF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((fcan hS.split (zcQF fr u) : Q) : G) = fr.zc (fval u⁻¹) := by
  rw [canon_zcQF fr hS u |>.1, zcQF_coe]

/-- `g (zc u) = zc u⁻¹` for `u ∈ F*`, coerced form. -/
theorem gcan_zcQF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((gcan hS.split (zcQF fr u) : Q) : G) = fr.zc (fval u⁻¹) := by
  rw [canon_zcQF fr hS u |>.2.1, zcQF_coe]

/-- `f (zc u) = zc u⁻¹`, element form. -/
lemma fcan_zcQF' (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    fcan hS.split (zcQF fr u) = zcQF fr u⁻¹ := (canon_zcQF fr hS u).1

/-- `g (zc u) = zc u⁻¹`, element form. -/
lemma gcan_zcQF' (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    gcan hS.split (zcQF fr u) = zcQF fr u⁻¹ := (canon_zcQF fr hS u).2.1

lemma zcQF_ne_one (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((zcQF fr u : Q) : G) ≠ 1 := by
  have hu2 : σE (fval u) = fval u := u.2
  rw [zcQF_coe]
  intro hc
  exact Units.ne_zero u (eq_zero_of_zc_eq_one fr hu2 hc)

lemma zcQF_ne (fr : CoarseFrame H Q t n) (u : ↥(FX n)) : zcQF fr u ≠ 1 :=
  fun h => zcQF_ne_one fr u (by rw [h]; rfl)

/-! ## `D` preserves `Q₀` -/

/-- Conjugation by an element of `H` preserves `Q₀sub H = fr.Q0`. -/
lemma conj_mem_Q0_of_mem_H (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {d : G}
    (hd : d ∈ H) {z : G} (hz : z ∈ fr.Q0) : d * z * d⁻¹ ∈ fr.Q0 := by
  rw [frameQ0_eq_Q0sub hS fr] at hz ⊢
  refine Subgroup.closure_induction (p := fun w _ => d * w * d⁻¹ ∈ Q0sub H) ?_ ?_ ?_ ?_ hz
  · intro w hw
    rw [Work.ThmF.mem_Q0_iff] at hw
    rcases hw with ⟨hwH, hword⟩ | rfl
    · refine Q0_le_Q0sub H ?_
      rw [Work.ThmF.mem_Q0_iff]
      left
      refine ⟨H.mul_mem (H.mul_mem hd hwH) (H.inv_mem hd), ?_⟩
      have hconj2 : (d * w * d⁻¹) ^ 2 = d * w ^ 2 * d⁻¹ := by rw [pow_two, pow_two]; group
      have hw2 : w ^ 2 = 1 := by
        have := pow_orderOf_eq_one w
        rwa [hword] at this
      have h2 : (d * w * d⁻¹) ^ 2 = 1 := by rw [hconj2, hw2, mul_one]; group
      have hne : d * w * d⁻¹ ≠ 1 := by
        intro hc
        have hh : w = 1 := by
          have h1 := congrArg (fun y => d⁻¹ * y * d) hc
          simpa [mul_assoc] using h1
        rw [hh, orderOf_one] at hword
        exact absurd hword (by norm_num)
      exact orderOf_eq_prime h2 hne
    · have h1 : d * (1 : G) * d⁻¹ = 1 := by group
      rw [h1]
      exact (Q0sub H).one_mem
  · show d * (1 : G) * d⁻¹ ∈ Q0sub H
    have h1 : d * (1 : G) * d⁻¹ = 1 := by group
    rw [h1]
    exact (Q0sub H).one_mem
  · intro u v _ _ hu hv
    have : d * (u * v) * d⁻¹ = (d * u * d⁻¹) * (d * v * d⁻¹) := by group
    rw [this]
    exact (Q0sub H).mul_mem hu hv
  · intro u _ hu
    have : d * u⁻¹ * d⁻¹ = (d * u * d⁻¹)⁻¹ := by group
    rw [this]
    exact (Q0sub H).inv_mem hu

/-- Conjugation by an element of `D = twoPoint H t` preserves `Q₀`. -/
lemma conj_mem_Q0_of_mem_D (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {d : G}
    (hd : d ∈ twoPoint H t) {z : G} (hz : z ∈ fr.Q0) : d * z * d⁻¹ ∈ fr.Q0 :=
  conj_mem_Q0_of_mem_H hS fr (twoPoint_le_left H t hd) hz

/-- `t`-conjugation preserves `D = twoPoint H t`. -/
lemma t_conj_mem_D (hS : PSU3Hyp H Q t) {d : G} (hd : d ∈ twoPoint H t) :
    t * d * t ∈ twoPoint H t := by
  obtain ⟨hdH, y, hyH, hyd⟩ := hd
  have htt : t * t = 1 := mul_self_eq_one hS.split
  have htinv : t⁻¹ = t := inv_eq_iff_mul_eq_one.mpr htt
  have hyd' : t * y * t⁻¹ = d := by simpa [MulAut.conj_apply] using hyd
  have hdeq : d = t * y * t := by rw [← hyd', htinv]
  refine ⟨?_, d, hdH, ?_⟩
  · have hAy : t * d * t = y := by
      rw [hdeq]
      calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [htt, mul_one, one_mul]
    rw [hAy]
    exact hyH
  · show (MulAut.conj t) d = t * d * t
    rw [MulAut.conj_apply, htinv]

/-! ## (W1): `f` preserves `Q₀` -/

/-- **(W1), forward.**  `f` maps `Q₀#` into `Q₀#`. -/
theorem fcan_mem_Q0_of_mem_Q0 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {w : Q}
    (hw : (w : G) ∈ fr.Q0) : ((fcan hS.split w : Q) : G) ∈ fr.Q0 := by
  rcases eq_or_ne (w : G) 1 with h1 | h1
  · have hw1 : w = 1 := Subtype.ext h1
    rw [hw1, fcan_apply_one hS.split]
    exact Q0_one_mem fr
  · obtain ⟨v, hv, hvz⟩ := fr.zc_surj (w : G) hw
    have hv0 : v ≠ 0 := by
      intro hc
      rw [hc, zc_zero fr] at hvz
      exact h1 hvz.symm
    have hwz : w = zcQF fr (mkFX v hv hv0) :=
      Subtype.ext (by rw [zcQF_coe, fval_mkFX]; exact hvz.symm)
    rw [hwz, fcan_zcQF hS fr (mkFX v hv hv0)]
    simp only [fval_inv, fval_mkFX]
    exact fr.zc_mem _ (by rw [map_inv₀, hv])

/-- **(W1), both directions.**  `f (w) ∈ Q₀ ↔ w ∈ Q₀`. -/
theorem fcan_mem_Q0_iff (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (w : Q) :
    ((fcan hS.split w : Q) : G) ∈ fr.Q0 ↔ (w : G) ∈ fr.Q0 := by
  refine ⟨?_, fcan_mem_Q0_of_mem_Q0 hS fr⟩
  intro h
  by_contra hw0
  have hw1 : (w : G) ≠ 1 := fun hc => hw0 (by rw [hc]; exact Q0_one_mem fr)
  have hf : ((fcan hS.split w : Q) : G) ≠ 1 := fcan_ne_one hS.split hw1
  obtain ⟨v, hv, hvz⟩ := fr.zc_surj ((fcan hS.split w : Q) : G) h
  have hv0 : v ≠ 0 := by
    intro hc
    rw [hc, zc_zero fr] at hvz
    exact hf hvz.symm
  have hfw : fcan hS.split w = zcQF fr (mkFX v hv hv0) :=
    Subtype.ext (by rw [zcQF_coe, fval_mkFX]; exact hvz.symm)
  have hff : ((fcan hS.split (fcan hS.split w) : Q) : G) = (w : G) :=
    (fcan_fcan hS.split hw1).1
  have h2 : (w : G) = fr.zc v⁻¹ := by
    rw [← hff, hfw, fcan_zcQF hS fr (mkFX v hv hv0)]
    simp only [fval_inv, fval_mkFX]
  rw [h2] at hw0
  exact hw0 (fr.zc_mem _ (by rw [map_inv₀, hv]))

/-! ## §2 (4) -/

/-- **§2 (4).**  If `ω ∉ Q₀`, `x, y ∈ Q₀` and `f (ω x) = f (ω) y`, then `x = 1`. -/
theorem fcan_shift_Q0 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : Q} (hω : (ω : G) ∉ fr.Q0) {x y : Q}
    (hx : (x : G) ∈ fr.Q0) (hy : (y : G) ∈ fr.Q0)
    (h : fcan hS.split (ω * x) = fcan hS.split ω * y) : (x : G) = 1 := by
  by_contra hx1
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hcomm : (x : G) * (ω : G) = (ω : G) * (x : G) := fr.Q0_central x hx ω ω.2
  have hxω_eq : (x * ω : Q) = ω * x := Subtype.ext hcomm
  have hxω_ne : ((x * ω : Q) : G) ≠ 1 := by
    intro hc
    have h' : (x : G) * (ω : G) = 1 := hc
    have h2 : (ω : G) = (x : G)⁻¹ := by
      calc (ω : G) = (x : G)⁻¹ * ((x : G) * (ω : G)) := by group
        _ = (x : G)⁻¹ * 1 := by rw [h']
        _ = (x : G)⁻¹ := by rw [mul_one]
    have hxinv : (x : G)⁻¹ = (x : G) := by
      have := Q0_mul_self fr hx
      exact inv_eq_of_mul_eq_one_right this
    exact hω (by rw [h2, hxinv]; exact hx)
  have h6 := (canon_mul_fun hS.split hx1 hω1 hxω_ne).1
  rw [hxω_eq, h] at h6
  set A : G := t * (hcan hS.split ω : G) * t with hA
  set F : G := (fcan hS.split ω : G) with hF
  set Z : G := (fcan hS.split (fcan hS.split x * gcan hS.split ω) : G) with hZ
  have hy_central : (y : G) * F = F * (y : G) :=
    fr.Q0_central y hy (fcan hS.split ω) (fcan hS.split ω).2
  have hZeq : Z = A * (y : G) * A⁻¹ := by
    have h2 : A⁻¹ * Z * A * F = F * (y : G) := by
      have h2' := h6.symm
      rw [Subgroup.coe_mul] at h2'
      exact h2'
    have h3 : A⁻¹ * Z * A = F * (y : G) * F⁻¹ := by rw [← h2]; group
    have h4 : F * (y : G) * F⁻¹ = (y : G) := by rw [← hy_central]; group
    rw [h4] at h3
    rw [← h3]; group
  have hAdD : A ∈ twoPoint H t := by
    rw [hA]
    exact t_conj_mem_D hS (hcan hS.split ω).2
  have hZQ0 : Z ∈ fr.Q0 := by
    rw [hZeq]
    exact conj_mem_Q0_of_mem_D hS fr hAdD hy
  have hfxQ0 : ((fcan hS.split x : Q) : G) ∈ fr.Q0 := fcan_mem_Q0_of_mem_Q0 hS fr hx
  have hfxgw : ((fcan hS.split x * gcan hS.split ω : Q) : G) ∈ fr.Q0 :=
    (fcan_mem_Q0_iff hS fr _).mp hZQ0
  have hgwQ0 : ((gcan hS.split ω : Q) : G) ∈ fr.Q0 := by
    have h2 : ((fcan hS.split x : Q) : G)⁻¹ * ((fcan hS.split x * gcan hS.split ω : Q) : G)
        ∈ fr.Q0 := (fr.Q0).mul_mem ((fr.Q0).inv_mem hfxQ0) hfxgw
    simpa using h2
  have hfw : ((fcan hS.split (ω⁻¹) : Q) : G) ∈ fr.Q0 := by
    have h3 : (fcan hS.split (ω⁻¹) : G) = ((gcan hS.split ω : Q) : G)⁻¹ :=
      fcan_inv hS.split hω1
    rw [h3]
    exact (fr.Q0).inv_mem hgwQ0
  have hwinv : ((ω⁻¹ : Q) : G) ∈ fr.Q0 := (fcan_mem_Q0_iff hS fr (ω⁻¹)).mp hfw
  exact hω (by simpa using (fr.Q0).inv_mem hwinv)

/-! ## §2 (2) and (3): the recursions along a `Q₀`-coset -/

/-- **§2 (2).** -/
theorem fcan_mul_zcQF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {x : Q} (hx : (x : G) ≠ 1) (u : ↥(FX n))
    (hxu : ((x * zcQF fr u : Q) : G) ≠ 1) :
    (fcan hS.split (x * zcQF fr u) : G) =
      (t * (hcan hS.split (zcQF fr u) : G) * t)⁻¹ *
        (fcan hS.split (fcan hS.split x * zcQF fr u⁻¹) : G) *
        (t * (hcan hS.split (zcQF fr u) : G) * t) * (zcQF fr u⁻¹ : G) := by
  have h6 := (canon_mul_fun hS.split hx (zcQF_ne_one fr u) hxu).1
  rw [h6, fcan_zcQF' hS fr u, gcan_zcQF' hS fr u]

/-- **§2 (3).** -/
theorem fcan_zcQF_mul (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (u : ↥(FX n)) {p : Q} (hp : (p : G) ≠ 1)
    (hzp : ((zcQF fr u * p : Q) : G) ≠ 1) :
    (fcan hS.split (zcQF fr u * p) : G) =
      (t * (hcan hS.split p : G) * t)⁻¹ *
        (fcan hS.split (zcQF fr u⁻¹ * gcan hS.split p) : G) *
        (t * (hcan hS.split p : G) * t) * (fcan hS.split p : G) := by
  have h6 := (canon_mul_fun hS.split (zcQF_ne_one fr u) hp hzp).1
  rw [h6, fcan_zcQF' hS fr u]

/-- The conjugation action `x ↦ d⁻¹ x d` of `KW ≤ D` on `Q`. -/
noncomputable def kact (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) (x : Q) : Q :=
  ⟨(d : G)⁻¹ * (x : G) * (d : G), by
    have hdH : (d : G) ∈ H := twoPoint_le_left H t (fr.KW_le d.2)
    have h := conj_mem_of_mem hS.split (H.inv_mem hdH) x.2
    simpa using h⟩

@[simp] lemma kact_coe (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) (x : Q) :
    ((kact hS fr d x : Q) : G) = (d : G)⁻¹ * (x : G) * (d : G) := rfl

lemma kact_bar (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) (x : Q) :
    Multiplicative.toAdd (fr.bar (kact hS fr d x)) =
      (fr.κ d : E n) * Multiplicative.toAdd (fr.bar x) :=
  fr.act_bar d x (kact hS fr d x) rfl

lemma kact_mul (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d e : fr.KW) (x : Q) :
    kact hS fr d (kact hS fr e x) = kact hS fr (e * d) x := by
  apply Subtype.ext
  simp only [kact_coe, Subgroup.coe_mul]
  group

lemma kact_one (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (x : Q) :
    kact hS fr 1 x = x := by
  apply Subtype.ext
  simp [kact_coe]

/-- The `KW`-orbit of `x ∈ Q`, up to `Q₀` (i.e. the set of `z` whose image in `Q/Q₀` is a
`KW`-multiple of that of `x`). -/
noncomputable def orbKW (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (x : Q) : Set Q :=
  {z | ∃ d : fr.KW, ∃ y : Q, (y : G) ∈ fr.Q0 ∧ z = kact hS fr d x * y}

/-- Characterisation of `orbKW` by the image in `E`: `z` is in the orbit of `x` iff some
`KW`-conjugate of `x` has the same image as `z`. -/
lemma mem_orbKW_iff (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (x z : Q) :
    z ∈ orbKW hS fr x ↔ ∃ d : fr.KW, fr.bar z = fr.bar (kact hS fr d x) := by
  constructor
  · rintro ⟨d, y, hy, rfl⟩
    exact ⟨d, by rw [map_mul, (fr.bar_eq_one_iff y).mpr hy, mul_one]⟩
  · rintro ⟨d, hd⟩
    refine ⟨d, (kact hS fr d x)⁻¹ * z, ?_, by group⟩
    rw [← fr.bar_eq_one_iff ((kact hS fr d x)⁻¹ * z), map_mul, map_inv, hd, inv_mul_cancel]

lemma orbKW_refl (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (x : Q) :
    x ∈ orbKW hS fr x :=
  ⟨1, 1, Q0_one_mem fr, by rw [kact_one, mul_one]⟩

/-- An element of `Q₀` has trivial image. -/
lemma bar_eq_one_of_Q0 (fr : CoarseFrame H Q t n) {a : Q} (ha : (a : G) ∈ fr.Q0) :
    fr.bar a = 1 := (fr.bar_eq_one_iff a).mpr ha

lemma orbKW_trans (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {x y z : Q}
    (hxy : y ∈ orbKW hS fr x) (hyz : z ∈ orbKW hS fr y) : z ∈ orbKW hS fr x := by
  rw [mem_orbKW_iff] at hxy hyz ⊢
  obtain ⟨d, hd⟩ := hxy
  obtain ⟨e, he⟩ := hyz
  refine ⟨d * e, ?_⟩
  have hy : ((y * (kact hS fr d x)⁻¹ : Q) : G) ∈ fr.Q0 := by
    rw [← fr.bar_eq_one_iff (y * (kact hS fr d x)⁻¹), map_mul, map_inv, hd, mul_inv_cancel]
  have hconj : ((kact hS fr e (y * (kact hS fr d x)⁻¹) : Q) : G) ∈ fr.Q0 := by
    have h := conj_mem_Q0_of_mem_D hS fr (fr.KW_le (e⁻¹).2) hy
    simpa [kact_coe, Subgroup.coe_inv] using h
  have h2 : (((kact hS fr e y) * (kact hS fr e (kact hS fr d x))⁻¹ : Q) : G) ∈ fr.Q0 := by
    have heq : ((kact hS fr e y) * (kact hS fr e (kact hS fr d x))⁻¹ : Q) =
        (kact hS fr e (y * (kact hS fr d x)⁻¹) : Q) := by
      apply Subtype.ext
      simp only [kact_coe, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [heq]
    exact hconj
  have hbar : fr.bar (kact hS fr e y) = fr.bar (kact hS fr e (kact hS fr d x)) := by
    have h := bar_eq_one_of_Q0 fr h2
    rw [map_mul, map_inv] at h
    exact mul_inv_eq_one.mp h
  rw [he, hbar, kact_mul hS fr e d x]

lemma orbKW_symm (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {x y : Q}
    (hxy : y ∈ orbKW hS fr x) : x ∈ orbKW hS fr y := by
  rw [mem_orbKW_iff] at hxy ⊢
  obtain ⟨d, hd⟩ := hxy
  refine ⟨d⁻¹, ?_⟩
  have hy : ((y * (kact hS fr d x)⁻¹ : Q) : G) ∈ fr.Q0 := by
    rw [← fr.bar_eq_one_iff (y * (kact hS fr d x)⁻¹), map_mul, map_inv, hd, mul_inv_cancel]
  have hconj : (((kact hS fr d⁻¹ y) * x⁻¹ : Q) : G) ∈ fr.Q0 := by
    have h := conj_mem_Q0_of_mem_D hS fr (fr.KW_le d.2) hy
    have h2 : (d : G) * ((y * (kact hS fr d x)⁻¹ : Q) : G) * (d : G)⁻¹
        = (((kact hS fr d⁻¹ y) * x⁻¹ : Q) : G) := by
      simp only [kact_coe, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [h2] at h
  have hbar : fr.bar (kact hS fr d⁻¹ y) = fr.bar x := by
    have h := bar_eq_one_of_Q0 fr hconj
    rw [map_mul, map_inv] at h
    exact mul_inv_eq_one.mp h
  exact hbar.symm



/-! ## The `KW`-orbits on `E` -/

/-- The `KW`-orbit of `α ∈ E` under the contragredient action `α ↦ κ(d) · α`. -/
noncomputable def orbE (fr : CoarseFrame H Q t n) (a : E n) : Set (E n) :=
  {b | ∃ d : fr.KW, b = (fr.κ d : E n) * a}

lemma mem_orbE_iff {fr : CoarseFrame H Q t n} {a b : E n} :
    b ∈ orbE fr a ↔ ∃ d : fr.KW, b = (fr.κ d : E n) * a := Iff.rfl

lemma orbE_refl (fr : CoarseFrame H Q t n) (a : E n) : a ∈ orbE fr a :=
  ⟨1, by simp⟩

/-- The image in `E` of an orbit in `Q` is the corresponding orbit in `E`. -/
lemma mem_orbKW_iff_orbE (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (x y : Q) :
    y ∈ orbKW hS fr x ↔
      Multiplicative.toAdd (fr.bar y) ∈ orbE fr (Multiplicative.toAdd (fr.bar x)) := by
  constructor
  · intro hy
    rw [mem_orbKW_iff] at hy
    obtain ⟨d, hd⟩ := hy
    exact ⟨d, by rw [hd, kact_bar]⟩
  · rintro ⟨d, hd⟩
    rw [mem_orbKW_iff]
    refine ⟨d, Multiplicative.toAdd.injective ?_⟩
    rw [kact_bar, hd]


/-! ## §2 (10): the exponent element `ζ a^{-2}` -/

/-- `ζ` as an element of `D = twoPoint H t`. -/
noncomputable def zetaD (fr : CoarseFrame H Q t n) : ↥(twoPoint H t) := ⟨fr.ζ, fr.KW_le fr.ζ.2⟩

/-- The exponent element `ζ · a^{-2}` of Ch. VII §2 (10), for `a = kElF (τ u)`. -/
noncomputable def zetaExp (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) : fr.KW :=
  fr.ζ * (kElF fr (tau hS fr u))⁻¹ * (kElF fr (tau hS fr u))⁻¹


end Work.PSU3.StageB
