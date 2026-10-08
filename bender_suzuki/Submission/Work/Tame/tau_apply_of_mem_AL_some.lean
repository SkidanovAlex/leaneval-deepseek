import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.tau_at_AL_v3
import Submission.Work.Tame.indFun_Lgrp_apply_of_mem_Lhat
import Submission.Work.Tame.conj_mul_notMem_Lhat
import Submission.Work.Tame.tau_eq_zero_of_not_isConj
import Submission.Work.Tame.mem_hatNp_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.tau_apply_of_mem_AL_some`

Feit–Thompson Lemma 9.1, value part (p. 805), in the shape needed for FT 9.2:

if `L̂` is tamely imbedded in the finite group `X` with supporting subgroups `𝔎_1, …, 𝔎_n`,
`𝔇 ≠ ∅`, `α ∈ 𝓒₀(L̂)`, `L ∈ 𝔏_i = Lset Lhat (Hs i)` and `H ∈ 𝔎_i = Hs i` commutes with `L`, then

`α^τ(L·H) = α(L)`.

The proof expands `α^τ = α^* + Σ_j (α_{j1} - α_{j2})^*` at `A = L·H`.

* The first summand `α^*(A)` vanishes when `H ≠ 1` (no conjugate of `A` lies in `L̂`, by
  `conj_mul_notMem_Lhat`) and is `|C(L)|·|C(L) ⊓ 𝔏|⁻¹·α(L)` when `H = 1`
  (`indFun_Lgrp_apply_of_mem_Lhat`).
* For `j ≠ i` the `j`-th correction term vanishes at `A` (`not_conj_mem_hatNp_of_mem_AL` and
  `indFun_beta_eq_zero_of_forall_not_conj`, or `indFun_beta_apply_self_eq_zero` for `H = 1`).
* For `j = i` and `H = 1` the `i`-th correction term is `β_i(L) = α(L) - |C(L) ⊓ 𝔎_i|·α(L)`
  (`indFun_beta_apply_self`, `beta_apply_self`), so that (9.3) `|C(L)| = |C(L) ⊓ 𝔎_i| · |C(L) ⊓ 𝔏|`
  (`card_centralizer_eq_mul`) cancels the first summand.
* For `j = i` and `H ≠ 1` the element `A` lies in `Ñ_i^#` (`mem_hatNp_of_mem_AL`), so the `i`-th
  correction term equals `β_i(A) = α_{i1}(A) - α_{i2}(A) = α(L) - 0`: `α_{i1}(A) = α(π A) = α(L)`
  because `π(L·H) = L` (the projection `π = projEC` is a homomorphism killing `𝔎_i`), and
  `α_{i2}(A) = 0` because `{k ∈ 𝔎_i | k⁻¹(L·H)k = L}` is empty (`|L·H| = |L|·|H| ≠ |L|`).
-/

noncomputable section

set_option maxHeartbeats 4000000

open Classical

namespace Work.Tame

variable {X : Type*} [Group X] [Fintype X]

/-- The induced function `Ind_𝔏^X α` vanishes at `A` if `α ∈ 𝓒(L̂)` (it vanishes off `L̂`) and no
conjugate of `A` lies in `L̂`. -/
theorem indFun_Lgrp_eq_zero_of_forall_notMem_conj {Lhat : Set X}
    {α : ↥(Lgrp Lhat) → ℂ}
    (hvan : ∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → α l = 0)
    {A : X} (hA : ∀ x : X, x * A * x⁻¹ ∉ Lhat) :
    Induction.indFun (Lgrp Lhat) α A = 0 := by
  rw [Induction.indFun_apply_def, mul_eq_zero]
  right
  refine Finset.sum_eq_zero (fun x _ => ?_)
  by_cases hx : x * A * x⁻¹ ∈ Lgrp Lhat
  · rw [dif_pos hx]
    exact hvan ⟨x * A * x⁻¹, hx⟩ (hA x)
  · rw [dif_neg hx]

/-- The `𝔏`-component of `L · H` is `L` when `L ∈ 𝔏_i = Lset Lhat (Hs i)` and `H ∈ 𝔎_i`:
`π = projEC` is a homomorphism and kills `𝔎_i`. -/
theorem projEC_mem_AL {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n} {L H : X}
    (hL : L ∈ Lset Lhat (Hs i)) (hH : H ∈ Hs i)
    (hΛ : L * H ∈ Lgrp (Hs i : Set X)) :
    projEC Lhat (Hs i) ⟨L * H, hΛ⟩
      = ⟨L, h.sub_norm hL.1.1, hL.2 (self_mem_centralizer L)⟩ := by
  have hLN : L ∈ Lgrp (Hs i : Set X) := hL.2 (self_mem_centralizer L)
  have hsup := h.supp_prod hne i
  have hinf := h.supp_inf hne i
  have hHN : H ∈ Lgrp (Hs i : Set X) := Subgroup.le_normalizer hH
  have hHone : projEC Lhat (Hs i) ⟨H, hHN⟩ = 1 :=
    projEC_eq_of hinf (m := 1) (by simpa using hH)
  have h1 : projEC Lhat (Hs i) ⟨L * H, hΛ⟩ = projEC Lhat (Hs i) ⟨L, hLN⟩ := by
    rw [show (⟨L * H, hΛ⟩ : ↥(Lgrp (Hs i : Set X))) = ⟨L, hLN⟩ * ⟨H, hHN⟩ from Subtype.ext rfl,
      projEC_mul hsup hinf, hHone, mul_one]
  rw [h1]
  exact projEC_eq_self hinf ⟨L, h.sub_norm hL.1.1, hLN⟩

/-- The count `#{k ∈ 𝔎_i | k⁻¹(L·H)k = L}` of (9.5) vanishes when `H ≠ 1`: `k⁻¹(L·H)k = L`
would make `L · H` conjugate to `L`, whence `|L·H| = |L|`, contradicting the coprimality of
`|L|` and `|H|` and `H ≠ 1`. -/
theorem card_alphaI2_mem_AL_eq_zero {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n} {L H : X}
    (hL : L ∈ Lset Lhat (Hs i)) (hH : H ∈ Hs i) (hH1 : H ≠ 1) (hcomm : H * L = L * H) :
    Nat.card {k : ↥(Hs i) // (k : X)⁻¹ * (L * H) * (k : X) = L} = 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  refine ⟨fun k => ?_⟩
  have hk : ((k : ↥(Hs i)) : X)⁻¹ * (L * H) * ((k : ↥(Hs i)) : X) = L := k.2
  have hLH_eq : L * H = ((k : ↥(Hs i)) : X) * L * (((k : ↥(Hs i)) : X))⁻¹ := by
    have hc := congrArg (fun t => ((k : ↥(Hs i)) : X) * t * (((k : ↥(Hs i)) : X))⁻¹) hk
    rwa [show ((k : ↥(Hs i)) : X) * (((k : ↥(Hs i)) : X)⁻¹ * (L * H) * ((k : ↥(Hs i)) : X)) *
      (((k : ↥(Hs i)) : X))⁻¹ = L * H from by group] at hc
  have hcop : (orderOf L).Coprime (orderOf H) :=
    (coprime_orderOf_of_mem_Lset_mem_Hs h hne hL hH).symm
  have h1 : orderOf (L * H) = orderOf L * orderOf H :=
    Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm.symm hcop
  have h2 : orderOf (((k : ↥(Hs i)) : X) * L * (((k : ↥(Hs i)) : X))⁻¹) = orderOf L := by
    have := orderOf_injective (MulAut.conj (((k : ↥(Hs i)) : X))).toMonoidHom
      (MulAut.conj (((k : ↥(Hs i)) : X))).injective L
    simpa using this
  have h3 : orderOf L * orderOf H = orderOf L := by rw [← h1, hLH_eq, h2]
  have h4 : orderOf L * orderOf H = orderOf L * 1 := by rw [h3, mul_one]
  have h5 : orderOf H = 1 := Nat.mul_left_cancel (orderOf_pos L) h4
  exact hH1 (orderOf_eq_one_iff.mp h5)

/-- `α_{i1}(L·H) = α(L)` for `L ∈ 𝔏_i`, `H ∈ 𝔎_i`. -/
theorem alphaI1LM_apply_mem_AL {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n} {L H : X}
    (hL : L ∈ Lset Lhat (Hs i)) (hH : H ∈ Hs i)
    {α : ↥(Lgrp Lhat) → ℂ} (hΛ : L * H ∈ Lgrp (Hs i : Set X)) :
    alphaI1LM Lhat (Hs i) α ⟨L * H, hΛ⟩ = α ⟨L, h.sub_norm hL.1.1⟩ := by
  rw [alphaI1LM_apply, projEC_mem_AL h hne hL hH hΛ]
  rfl

/-- `α_{i2}(L·H) = 0` for `L ∈ 𝔏_i`, `H ∈ 𝔎_i`, `H ≠ 1` (by (9.5) and the vanishing of the
count `#{k ∈ 𝔎_i | k⁻¹(L·H)k = L}`). -/
theorem alphaI2LM_apply_mem_AL_eq_zero {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n} {L H : X}
    (hL : L ∈ Lset Lhat (Hs i)) (hH : H ∈ Hs i) (hH1 : H ≠ 1) (hcomm : H * L = L * H)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) (hΛ : L * H ∈ Lgrp (Hs i : Set X)) :
    alphaI2LM Lhat (Hs i) α ⟨L * H, hΛ⟩ = 0 := by
  rw [alphaI2LM_apply_eq_card h hne i hα ⟨L * H, hΛ⟩]
  rw [projEC_mem_AL h hne hL hH hΛ]
  have hcard := card_alphaI2_mem_AL_eq_zero h hne hL hH hH1 hcomm
  rw [hcard, Nat.cast_zero, zero_mul]

/-- The value part of Lemma 9.1 at `A = L ∈ 𝔏_i` (the case `H = 1`). -/
theorem tau_apply_self_mem_Lset {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {i : Fin n} {L : X}
    (hL : L ∈ Lset Lhat (Hs i)) :
    tau Lhat n Hs α L = α ⟨L, h.sub_norm hL.1.1⟩ := by
  rw [tau_apply]
  rw [indFun_Lgrp_apply_of_mem_Lhat h hα hL.1.1 hL.1.2.1]
  rw [Finset.sum_eq_single i
      (fun j _ hj => indFun_beta_apply_self_eq_zero (L := ⟨L, h.sub_norm hL.1.1⟩) h hD hj hL hα)
      (fun hh => absurd (Finset.mem_univ i) hh)]
  rw [indFun_beta_apply_self (L := ⟨L, h.sub_norm hL.1.1⟩) h hD hL hα]
  rw [beta_apply_self (L := ⟨L, h.sub_norm hL.1.1⟩) h hD hL hα]
  have hcard : (Nat.card ↥(Subgroup.centralizer ({L} : Set X)) : ℂ) *
      (Nat.card ↥(Subgroup.centralizer ({L} : Set X) ⊓ Lgrp Lhat) : ℂ)⁻¹ =
      (Nat.card ↥(Subgroup.centralizer ({L} : Set X) ⊓ Hs i) : ℂ) := by
    have h3 := card_centralizer_eq_mul h hD hL
    have hne : (Nat.card ↥(Subgroup.centralizer ({L} : Set X) ⊓ Lgrp Lhat) : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Nat.card_ne_zero.mpr ⟨⟨⟨1, (Subgroup.centralizer ({L} : Set X) ⊓ Lgrp Lhat).one_mem⟩⟩,
        inferInstance⟩
    rw [h3, Nat.cast_mul, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [hcard]
  ring

/-- The value part of Lemma 9.1 at `A = L·H` with `H ∈ 𝔎_i`, `H ≠ 1` (so `A ∈ Ñ_i^#`). -/
theorem tau_apply_mem_AL_ne_one {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {i : Fin n} {L H : X}
    (hL : L ∈ Lset Lhat (Hs i)) (hH : H ∈ Hs i) (hH1 : H ≠ 1) (hcomm : L * H = H * L) :
    tau Lhat n Hs α (L * H) = α ⟨L, h.sub_norm hL.1.1⟩ := by
  have hLN' : L ∈ Lgrp (Hs i : Set X) := hL.2 (self_mem_centralizer L)
  have hHN : H ∈ Lgrp (Hs i : Set X) := Subgroup.le_normalizer hH
  have hΛ : L * H ∈ Lgrp (Hs i : Set X) := (Lgrp (Hs i : Set X)).mul_mem hLN' hHN
  have hcomm' : H * L = L * H := hcomm.symm
  have hAnp : L * H ∈ hatNp (Hs i) := mem_hatNp_of_mem_AL h hD hL hH hH1 hcomm'
  rw [tau_apply]
  rw [indFun_Lgrp_eq_zero_of_forall_notMem_conj (fun l hl => (mem_C0.mp hα).2.1 l hl) (fun x hx =>
    conj_mul_notMem_Lhat h hD hL hH hH1 hcomm' (x * (L * H) * x⁻¹) hx
      (isConj_iff.mpr ⟨x, by rw [hcomm]⟩))]
  rw [Finset.sum_eq_single i
      (fun j _ hj => indFun_beta_eq_zero_of_forall_not_conj h hD hα j
        (fun x => not_conj_mem_hatNp_of_mem_AL h hD hj hL hH hH1 hcomm'))
      (fun hh => absurd (Finset.mem_univ i) hh)]
  rw [indFun_eq_of_mem_hatNp h hD i (isClassFun_beta h hD hα i)
    (fun N hN => beta_eq_zero_of_notMem_hatNp h hD hα i hN) (N := ⟨L * H, hΛ⟩) hAnp]
  have hbeta : ((alphaI1LM Lhat (Hs i)) α - (alphaI2LM Lhat (Hs i)) α) ⟨L * H, hΛ⟩
      = α ⟨L, h.sub_norm hL.1.1⟩ := by
    rw [Pi.sub_apply, alphaI1LM_apply_mem_AL h hD hL hH hΛ,
      alphaI2LM_apply_mem_AL_eq_zero h hD hL hH hH1 hcomm' hα hΛ, sub_zero]
  rw [hbeta, zero_add]

theorem tau_apply_of_mem_AL_some {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : Work.Tame.IsTamelyImbedded Lhat n Hs)
    (hD : (Work.Tame.Dset Lhat).Nonempty) {α : ↥(Work.Tame.Lgrp Lhat) → ℂ}
    (hα : α ∈ Work.Tame.C0 Lhat) {i : Fin n} {L H : X} (hL : L ∈ Work.Tame.Lset Lhat (Hs i))
    (hH : H ∈ Hs i) (hcomm : L * H = H * L) :
    Work.Tame.tau Lhat n Hs α (L * H) = α ⟨L, h.sub_norm hL.1.1⟩ := by
  by_cases hH1 : H = 1
  · rw [hH1, mul_one]
    exact tau_apply_self_mem_Lset h hD hα hL
  · exact tau_apply_mem_AL_ne_one h hD hα hL hH hH1 hcomm

end Work.Tame
