import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.irr_vanishes_off_hatN
import Submission.Work.Tame.tau_apply_one
import Submission.Work.Tame.tau_eq_zero_of_not_isConj
import Submission.Work.Tame.mem_AU_iff
import Submission.Work.Tame.inConjAU_iff
import Submission.Work.Tame.tau_at_AL_v3
import Submission.Work.Tame.alphaI1_isClassFun
import Submission.Work.Tame.alphaI2_apply_eq_zero_of_not_inConjAU
import Submission.Work.Tame.centralizer_le_normalizer_of_mem_hatNp
import Submission.Work.Tame.conj_mem_hatNp_and_notMem
import Submission.Work.Tame.isConj_projEC_of_coprime_order
import Submission.Work.Tame.tau_apply_of_mem_AL_some
import Submission.Work.Tame.cfInner_const_coset_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.lem92b` — Feit–Thompson Lemma 9.2, second part

For a tamely imbedded subset `L̂` of a finite group `X` with supporting subgroups `𝔎_1, …, 𝔎_n` and
`𝔇 ≠ ∅`, for `α ∈ 𝓒₀(L̂)` and for an irreducible character `θ` of `𝔑_i = N(𝔎_i)` which is not
trivial on `𝔎_i`, the restriction of `α^τ` (the Dade map (9.4)) to `𝔑_i` is orthogonal to `θ`:

  `(α^τ|_{𝔑_i}, θ)_{𝔑_i} = 0`.

The argument follows Feit–Thompson pp. 806–807.  By Lemma 4.3 (`irr_vanishes_off_hatN`), `θ`
vanishes on `𝔑_i − Ñ_i − 𝔎_i`, and by the first part of Lemma 9.2 one has the pointwise identity

  `α^τ(N) = α_{i1}(N)`   for `N ∈ Ñ_i ∪ 𝔎_i`

(`tau_eq_alphaI1_of_mem_Hs`, `tau_eq_alphaI1_of_mem_hatNp`).  Hence the two inner products
`(α^τ|_{𝔑_i}, θ)` and `(α_{i1}, θ)` agree; and `α_{i1}` is the inflation of the class function
of `𝔑_i/𝔎_i` obtained from `α|_{𝔏 ∩ 𝔑_i}`, so it is orthogonal to `θ` because `θ` is not trivial
on `𝔎_i` (`cfInner_const_coset_eq_zero`).
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Tame

variable {X : Type*} [Group X] [Fintype X]

/-! ## Elementary auxiliary lemmas -/

/-- A class function takes the same value at conjugate elements. -/
theorem lem92b_classFun_apply_of_isConj {f : X → ℂ} (hf : CharCore.IsClassFun f) {a b : X}
    (h : IsConj a b) : f a = f b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact (hf a c).symm

/-- Conjugate elements have the same order. -/
theorem lem92b_orderOf_eq_of_isConj {a b : X} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a).symm

/-- The order of an element of a subgroup divides the order of the subgroup. -/
theorem lem92b_orderOf_dvd_natCard_of_mem {K : Subgroup X} {x : X} (hx : x ∈ K) :
    orderOf x ∣ Nat.card K := by
  have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥K)
  simpa [Subgroup.orderOf_coe] using h1

/-- The order of a commuting product of an element of `𝔏_i` and an element of `𝔎_i` is the
product of the orders (they are coprime, by Definition 9.1(ii)(b),(d)). -/
theorem lem92b_orderOf_mul_mem_AL {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty) {i : Fin n} {L H : X}
    (hL : L ∈ Lset Lhat (Hs i)) (hH : H ∈ Hs i) (hcomm : L * H = H * L) :
    orderOf (L * H) = orderOf L * orderOf H :=
  Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm
    (coprime_orderOf_of_mem_Lset_mem_Hs h hD hL hH).symm

/-- If an irreducible character `θ` of `𝔑 = N(𝔎)` has `⟨θ|_𝔎, 1_𝔎⟩ = 0` then it is not
trivial on `𝔎`: there is `H ∈ 𝔎` with `θ H ≠ θ 1`. -/
theorem lem92b_exists_mem_apply_ne_one_of_cfInner_eq_zero {K : Subgroup X}
    {θ : ↥(Lgrp (K : Set X)) → ℂ} (hθ : θ ∈ CharCore.Irr ↥(Lgrp (K : Set X)))
    (hθker : Coherence.cfInner (fun hh : ↥K => θ ⟨(hh : X), K.le_normalizer hh.2⟩)
      (1 : ↥K → ℂ) = 0) :
    ∃ H : ↥K, θ ⟨(H : X), K.le_normalizer H.2⟩ ≠ θ 1 := by
  by_contra h
  push_neg at h
  have hconst : (fun hh : ↥K => θ ⟨(hh : X), K.le_normalizer hh.2⟩) =
      (θ 1) • (1 : ↥K → ℂ) := by
    funext hh
    rw [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact h hh
  rw [hconst, Coherence.cfInner_smul_left] at hθker
  have hone : Coherence.cfInner (1 : ↥K → ℂ) (1 : ↥K → ℂ) = 1 := by
    rw [Coherence.cfInner_apply]
    simp only [Pi.one_apply, map_one, mul_one]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [hone, mul_one] at hθker
  have hne : θ 1 ≠ 0 := by
    rw [CharCore.irrDeg_spec hθ]
    exact CharCore.irrDeg_ne_zero hθ
  exact hne hθker

/-- For `L ∈ L̂^#` the order of `L` is coprime to `|𝔎_i|` (Definition 9.1(ii)(d)). -/
theorem lem92b_coprime_card_orderOf_of_mem_Lhat {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    (i : Fin n) {l : X} (hl : l ∈ Lhat) (hl1 : l ≠ 1) :
    (Nat.card (Hs i)).Coprime (orderOf l) := by
  have hldvd : orderOf l ∣ Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({l} : Set X)) := by
    have hmem : l ∈ (Lgrp Lhat ⊓ Subgroup.centralizer ({l} : Set X) : Subgroup X) :=
      ⟨h.sub_norm hl, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have h1 : orderOf (⟨l, hmem⟩ : ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({l} : Set X))) ∣
        Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({l} : Set X)) :=
      orderOf_dvd_natCard _
    simpa [Subgroup.orderOf_coe] using h1
  exact (h.supp_coprime_cent hD i l hl hl1).coprime_dvd_right hldvd

/-- The Dade map `τ` of (9.4) is a sum of induced functions, hence a class function of `X`. -/
theorem lem92b_isClassFun_tau (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (α : ↥(Lgrp Lhat) → ℂ) : CharCore.IsClassFun (tau Lhat n Hs α) := by
  have heq : tau Lhat n Hs α = Induction.indFun (Lgrp Lhat) α +
      ∑ i : Fin n, Induction.indFun (Lgrp (Hs i : Set X))
        (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) := by
    funext x
    rw [tau_apply]
    simp only [Pi.add_apply, Finset.sum_apply]
  rw [heq]
  exact (Work.Induction.isClassFun_indFun _ _).add
    (CharCore.IsClassFun.sum _ _ (fun i _ => Work.Induction.isClassFun_indFun _ _))

/-! ## The `𝔎_i` case of Lemma 9.2 -/

/-- No non-identity element of `𝔎_i` is conjugate to an element of `AU`, so in particular
`¬ inConjAU` holds at it (Feit–Thompson Lemma 9.2, the `𝔎_i` case). -/
theorem lem92b_not_inConjAU_of_mem_Hs_ne_one {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty) {i : Fin n} {N : X}
    (hN : N ∈ Hs i) (hN1 : N ≠ 1) : ¬ inConjAU Lhat n Hs N := by
  intro hAU
  obtain ⟨A, hA, hc⟩ := (inConjAU_iff h).mp hAU
  have hord : orderOf N = orderOf A :=
    lem92b_orderOf_eq_of_isConj hc
  have hdvdN : orderOf N ∣ Nat.card (Hs i) := lem92b_orderOf_dvd_natCard_of_mem hN
  rw [mem_AU_iff] at hA
  rcases hA with hA | ⟨j, L, hL, H, hH, hcomm, hAeq⟩
  · have h1 : orderOf A ∣ Nat.card (Hs i) := hord ▸ hdvdN
    have h2 : (Nat.card (Hs i)).Coprime (orderOf A) :=
      lem92b_coprime_card_orderOf_of_mem_Lhat h hD i hA.1 hA.2.1
    have h3 : orderOf A = 1 := by
      have hh : orderOf A ∣ Nat.gcd (Nat.card (Hs i)) (orderOf A) := Nat.dvd_gcd h1 (dvd_refl _)
      rw [h2.gcd_eq_one] at hh
      exact Nat.dvd_one.mp hh
    exact hA.2.1 (orderOf_eq_one_iff.mp h3)
  · have h1 : orderOf A ∣ Nat.card (Hs i) := hord ▸ hdvdN
    have hordA : orderOf A = orderOf L * orderOf H := by
      rw [hAeq]
      exact lem92b_orderOf_mul_mem_AL h hD hL hH hcomm
    have h2 : (Nat.card (Hs i)).Coprime (orderOf L) :=
      lem92b_coprime_card_orderOf_of_mem_Lhat h hD i hL.1.1 hL.1.2.1
    have h4 : orderOf L ∣ Nat.card (Hs i) :=
      dvd_trans (by rw [hordA]; exact dvd_mul_right _ _) h1
    have h5 : orderOf L = 1 := by
      have hh : orderOf L ∣ Nat.gcd (Nat.card (Hs i)) (orderOf L) := Nat.dvd_gcd h4 (dvd_refl _)
      rw [h2.gcd_eq_one] at hh
      exact Nat.dvd_one.mp hh
    exact hL.1.2.1 (orderOf_eq_one_iff.mp h5)

/-- **Feit–Thompson Lemma 9.2, first part, the `𝔎_i` case**: for `N ∈ 𝔎_i` one has
`α^τ(N) = α_{i1}(N) = 0`. -/
theorem lem92b_tau_eq_alphaI1_of_mem_Hs {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {i : Fin n}
    {N : ↥(Lgrp (Hs i : Set X))} (hN : (N : X) ∈ Hs i) :
    tau Lhat n Hs α (N : X) = alphaI1LM Lhat (Hs i) α N := by
  have hinf : Hs i ⊓ Lgrp Lhat = ⊥ := h.supp_inf hD i
  have hproj : projEC Lhat (Hs i) N = 1 :=
    projEC_eq_of (m := 1) hinf (by rw [Subgroup.coe_one, inv_one, mul_one]; exact hN)
  have hα1 : alphaI1LM Lhat (Hs i) α N = 0 := by
    rw [alphaI1LM_apply, hproj, map_one, hα.2.2]
  rw [hα1]
  by_cases hN1 : (N : X) = 1
  · rw [hN1]
    exact tau_apply_one (fun j => h.supp_inf hD j) hα.2.2
  · exact tau_eq_zero_of_not_isConj h (Or.inl hD) hα
      (lem92b_not_inConjAU_of_mem_Hs_ne_one h hD hN hN1)

/-! ## The `Ñ_i^#` case of Lemma 9.2 -/

/-- **Key computation.**  If `a ∈ Ñ_i^#` is conjugate to `N ∈ Ñ_i^#` by an element `x` of
`𝔑_i = N(𝔎_i)`, then `π_i(N)` and `π_i(a)` are conjugate in `𝔏 = N(L̂)`, so `α` (a class
function of `𝔏`) takes the same value on them. -/
theorem lem92b_alpha_apply_projEC_eq_of_isConj {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    {α : ↥(Lgrp Lhat) → ℂ} (hαc : CharCore.IsClassFun α) {i : Fin n}
    {N : ↥(Lgrp (Hs i : Set X))} {a : X} (ha : a ∈ hatNp (Hs i))
    {x : X} (hx : x * (N : X) * x⁻¹ = a) (hxmem : x ∈ Lgrp (Hs i : Set X)) :
    α (Subgroup.inclusion (inf_le_left : Lgrp Lhat ⊓ Lgrp (Hs i : Set X) ≤ Lgrp Lhat)
        (projEC Lhat (Hs i) N))
      = α (Subgroup.inclusion (inf_le_left : Lgrp Lhat ⊓ Lgrp (Hs i : Set X) ≤ Lgrp Lhat)
        (projEC Lhat (Hs i) ⟨a, (mem_hatNp_iff.mp ha).1⟩)) := by
  have hsup : Lgrp (Hs i : Set X) = Hs i ⊔ (Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) :=
    h.supp_prod hD i
  have hinf : Hs i ⊓ Lgrp Lhat = ⊥ := h.supp_inf hD i
  set x' : ↥(Lgrp (Hs i : Set X)) := ⟨x, hxmem⟩ with hx'def
  have hconj : x' * N * x'⁻¹ = (⟨a, (mem_hatNp_iff.mp ha).1⟩ : ↥(Lgrp (Hs i : Set X))) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx'def]
    exact hx
  have hp : projEC Lhat (Hs i) (⟨a, (mem_hatNp_iff.mp ha).1⟩ : ↥(Lgrp (Hs i : Set X)))
      = projEC Lhat (Hs i) x' * projEC Lhat (Hs i) N * (projEC Lhat (Hs i) x')⁻¹ := by
    rw [← hconj,
      projEC_mul_of_sup hsup hinf (x' * N) x'⁻¹,
      projEC_mul_of_sup hsup hinf x' N,
      projEC_inv_of_sup hsup hinf x']
  have h1 : Subgroup.inclusion (inf_le_left : Lgrp Lhat ⊓ Lgrp (Hs i : Set X) ≤ Lgrp Lhat)
      (projEC Lhat (Hs i) x' * projEC Lhat (Hs i) N * (projEC Lhat (Hs i) x')⁻¹)
      = Subgroup.inclusion inf_le_left (projEC Lhat (Hs i) x') *
        Subgroup.inclusion inf_le_left (projEC Lhat (Hs i) N) *
        (Subgroup.inclusion inf_le_left (projEC Lhat (Hs i) x'))⁻¹ := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
  rw [hp, h1]
  simpa using (hαc (Subgroup.inclusion inf_le_left (projEC Lhat (Hs i) N))
    (Subgroup.inclusion inf_le_left (projEC Lhat (Hs i) x'))).symm

/-- **The bad case is impossible.**  No element of `Ñ_i^#` is conjugate to a product `L * H` with
`L ∈ 𝔏_j`, `H ∈ 𝔎_j^#` and `L * H = H * L` for an index `j ≠ i`. -/
theorem lem92b_not_isConj_mul_of_mem_hatNp {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    {i j : Fin n} (hij : j ≠ i) {N : X} (hN : N ∈ hatNp (Hs i))
    {L H : X} (hL : L ∈ Lset Lhat (Hs j)) (hH : H ∈ Hs j) (hH1 : H ≠ 1)
    (hcomm : L * H = H * L) : ¬ IsConj N (L * H) := by
  intro hconj
  have hLhat : L ∈ Lhat := hL.1.1
  have hL1 : L ≠ 1 := hL.1.2.1
  have hLN : L ∈ Lgrp Lhat := h.sub_norm hLhat
  have hL𝔑 : L ∈ Lgrp (Hs j : Set X) :=
    hL.2 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hH𝔑 : H ∈ Lgrp (Hs j : Set X) := Subgroup.le_normalizer hH
  -- `L * H ∈ Ñ_j^#`
  have hA𝔑 : L * H ∈ Lgrp (Hs j : Set X) := (Lgrp (Hs j : Set X)).mul_mem hL𝔑 hH𝔑
  have hAK : L * H ∉ (Hs j : Set X) := by
    intro hmem
    have hLK : L ∈ (Hs j : Set X) := by
      have h3 : H⁻¹ ∈ (Hs j : Set X) := (Hs j).inv_mem hH
      have h4 : (L * H) * H⁻¹ ∈ (Hs j : Set X) := (Hs j).mul_mem hmem h3
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h4
    have h1 : L ∈ (Hs j ⊓ Lgrp Lhat : Subgroup X) := ⟨hLK, hLN⟩
    rw [h.supp_inf hD j, Subgroup.mem_bot] at h1
    exact hL1 h1
  have hAH : (L * H) * H = H * (L * H) := by
    have h1 : (L * H) * H = (H * L) * H := by rw [hcomm]
    rw [h1, mul_assoc H L H]
  have hAtp : L * H ∈ hatNp (Hs j) := mem_hatNp_iff.mpr ⟨hA𝔑, hAK, H, hH, hH1, hAH⟩
  have hCA : Subgroup.centralizer ({L * H} : Set X) ≤ Lgrp (Hs j : Set X) :=
    centralizer_le_normalizer_of_mem_hatNp (h.supp_ti hD j) (h.supp_hatN_norm hD j) hAtp
  -- an element of `𝔎_i^#` commuting with `N`
  obtain ⟨H_i, hH_iK, hH_i1, hH_icomm⟩ := (mem_hatNp_iff.mp hN).2.2
  obtain ⟨x, hx⟩ := isConj_iff.mp hconj
  -- `x H_i x⁻¹` commutes with `L * H`, hence lies in `𝔑_j`
  have hH_i'C : x * H_i * x⁻¹ ∈ Subgroup.centralizer ({L * H} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hx]
    calc (x * H_i * x⁻¹) * (x * N * x⁻¹) = x * (H_i * N) * x⁻¹ := by group
      _ = x * (N * H_i) * x⁻¹ := by rw [← hH_icomm]
      _ = (x * N * x⁻¹) * (x * H_i * x⁻¹) := by group
  have hH_i'N : x * H_i * x⁻¹ ∈ Lgrp (Hs j : Set X) := hCA hH_i'C
  have hordH : orderOf (x * H_i * x⁻¹) = orderOf H_i := by
    have hs : SemiconjBy x H_i (x * H_i * x⁻¹) := by
      change x * H_i = (x * H_i * x⁻¹) * x
      group
    exact hs.orderOf_eq.symm
  have hdvdH : orderOf H_i ∣ Nat.card (Hs i) := lem92b_orderOf_dvd_natCard_of_mem hH_iK
  have hcop : (orderOf (x * H_i * x⁻¹)).Coprime (Nat.card (Hs j)) := by
    rw [hordH]
    exact (h.supp_coprime hD i j (Ne.symm hij)).coprime_dvd_left hdvdH
  -- the projection `y ∈ 𝔏 ⊓ 𝔑_j` of `x H_i x⁻¹` is conjugate to it and commutes with `L`
  set w : ↥(Lgrp (Hs j : Set X)) := ⟨x * H_i * x⁻¹, hH_i'N⟩ with hwdef
  set y : ↥(Lgrp Lhat ⊓ Lgrp (Hs j : Set X)) := projEC Lhat (Hs j) w with hydef
  have hyconj : IsConj (x * H_i * x⁻¹) ((y : X)) :=
    isConj_projEC_of_coprime_order h hD j hH_i'N hcop
  have hyne : (y : X) ≠ 1 := by
    intro h1
    have h2 : orderOf (x * H_i * x⁻¹) = 1 := by
      rw [lem92b_orderOf_eq_of_isConj hyconj, h1, orderOf_one]
    exact hH_i1 (orderOf_eq_one_iff.mp (by rw [← hordH]; exact h2))
  have hprojA : projEC Lhat (Hs j) ⟨L * H, hA𝔑⟩ =
      (⟨(L : X), ⟨hLN, hL𝔑⟩⟩ : ↥(Lgrp Lhat ⊓ Lgrp (Hs j : Set X))) := by
    have hEq : (⟨L * H, hA𝔑⟩ : ↥(Lgrp (Hs j : Set X))) =
        ⟨(L : X), hL𝔑⟩ * ⟨H, hH𝔑⟩ := rfl
    have hstep : projEC Lhat (Hs j) (⟨(L : X), hL𝔑⟩ * ⟨H, hH𝔑⟩) =
        (⟨(L : X), ⟨hLN, hL𝔑⟩⟩ : ↥(Lgrp Lhat ⊓ Lgrp (Hs j : Set X))) := by
      rw [projEC_mul (h.supp_prod hD j) (h.supp_inf hD j) ⟨(L : X), hL𝔑⟩ ⟨H, hH𝔑⟩,
        projEC_eq_self (h.supp_inf hD j) ⟨(L : X), hLN, hL𝔑⟩]
      rw [projEC_eq_of (h.supp_inf hD j) (m := 1) (by
        rw [Subgroup.coe_one, inv_one, mul_one]; exact hH), mul_one]
    rw [hEq, hstep]
  have hycomm : (y : X) * L = L * (y : X) := by
    have h1 : w * ⟨L * H, hA𝔑⟩ = ⟨L * H, hA𝔑⟩ * w := by
      apply Subtype.ext
      show (w : X) * (L * H) = (L * H) * (w : X)
      rw [hwdef]
      rw [← hx]
      calc (x * H_i * x⁻¹) * (x * N * x⁻¹) = x * (H_i * N) * x⁻¹ := by group
        _ = x * (N * H_i) * x⁻¹ := by rw [← hH_icomm]
        _ = (x * N * x⁻¹) * (x * H_i * x⁻¹) := by group
    have h2 := congrArg (fun t : ↥(Lgrp (Hs j : Set X)) => projEC Lhat (Hs j) t) h1
    rw [projEC_mul (h.supp_prod hD j) (h.supp_inf hD j) w ⟨L * H, hA𝔑⟩,
      projEC_mul (h.supp_prod hD j) (h.supp_inf hD j) ⟨L * H, hA𝔑⟩ w, hprojA] at h2
    have h3 : projEC Lhat (Hs j) w = y := hydef.symm
    rw [h3] at h2
    exact congrArg (fun t : ↥(Lgrp Lhat ⊓ Lgrp (Hs j : Set X)) => (t : X)) h2
  -- contradiction with (ii)(d)
  have hycent : (y : X) ∈ Lgrp Lhat ⊓ Subgroup.centralizer ({L} : Set X) :=
    ⟨y.2.1, Subgroup.mem_centralizer_singleton_iff.mpr hycomm⟩
  have hdy : orderOf (y : X) ∣
      Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({L} : Set X)) :=
    lem92b_orderOf_dvd_natCard_of_mem hycent
  have hdyi : orderOf (y : X) ∣ Nat.card (Hs i) := by
    rw [← lem92b_orderOf_eq_of_isConj hyconj, hordH]
    exact hdvdH
  have hcopic := h.supp_coprime_cent hD i L hLhat hL1
  have hone : orderOf (y : X) = 1 := by
    have hh : orderOf (y : X) ∣ Nat.gcd (Nat.card (Hs i))
        (Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({L} : Set X))) :=
      Nat.dvd_gcd hdyi hdy
    rw [hcopic.gcd_eq_one] at hh
    exact Nat.dvd_one.mp hh
  exact hyne (orderOf_eq_one_iff.mp hone)

/-- **Feit–Thompson Lemma 9.2, first part, the `Ñ_i^#` case**: for `N ∈ Ñ_i^#` one has
`α^τ(N) = α_{i1}(N)`. -/
theorem lem92b_tau_eq_alphaI1_of_mem_hatNp {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : (Dset Lhat).Nonempty)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {i : Fin n}
    {N : ↥(Lgrp (Hs i : Set X))} (hN : (N : X) ∈ hatNp (Hs i)) :
    tau Lhat n Hs α (N : X) = alphaI1LM Lhat (Hs i) α N := by
  classical
  have hTI := conj_mem_hatNp_and_notMem h hD i
  have hαc : CharCore.IsClassFun α := hα.1
  by_cases hAU : inConjAU Lhat n Hs (N : X)
  · obtain ⟨A, hA, hcnj⟩ := (inConjAU_iff h).mp hAU
    rw [mem_AU_iff] at hA
    rcases hA with hA0 | ⟨j, L, hL, H, hH, hcomm, hAeq⟩
    · -- `A ∈ 𝔏_0`: impossible, since `N` is a conjugate of `A`
      exfalso
      obtain ⟨x, hx⟩ := isConj_iff.mp hcnj
      have h1 : x⁻¹ * A * x⁻¹⁻¹ ∉ hatNp (Hs i) :=
        not_isConj_mem_hatNp_of_mem_L0set h hD hA0 (x := x⁻¹)
      rw [inv_inv] at h1
      have h2 : x⁻¹ * A * x = (N : X) := by rw [← hx]; group
      rw [h2] at h1
      exact h1 hN
    · -- `A = L * H`
      have hLhat : L ∈ Lhat := hL.1.1
      have hL1 : L ≠ 1 := hL.1.2.1
      have hLN : L ∈ Lgrp Lhat := h.sub_norm hLhat
      have hL𝔑j : L ∈ Lgrp (Hs j : Set X) :=
        hL.2 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      have hH𝔑j : H ∈ Lgrp (Hs j : Set X) := Subgroup.le_normalizer hH
      have hA𝔑j : L * H ∈ Lgrp (Hs j : Set X) := (Lgrp (Hs j : Set X)).mul_mem hL𝔑j hH𝔑j
      have hAKj : L * H ∉ (Hs j : Set X) := by
        intro hmem
        have hLK : L ∈ (Hs j : Set X) := by
          have h3 : H⁻¹ ∈ (Hs j : Set X) := (Hs j).inv_mem hH
          have h4 : (L * H) * H⁻¹ ∈ (Hs j : Set X) := (Hs j).mul_mem hmem h3
          rwa [mul_assoc, mul_inv_cancel, mul_one] at h4
        have h1 : L ∈ (Hs j ⊓ Lgrp Lhat : Subgroup X) := ⟨hLK, hLN⟩
        rw [h.supp_inf hD j, Subgroup.mem_bot] at h1
        exact hL1 h1
      have hAHj : (L * H) * H = H * (L * H) := by
        have h1 : (L * H) * H = (H * L) * H := by rw [hcomm]
        rw [h1, mul_assoc H L H]
      -- `τ(α)(N) = τ(α)(A) = α L` (the value part of Lemma 9.1)
      have hτ : tau Lhat n Hs α (N : X) = α ⟨L, hLN⟩ := by
        have hcnj' : IsConj (N : X) (L * H) := hAeq ▸ hcnj
        have h1 : tau Lhat n Hs α (L * H) = α ⟨L, h.sub_norm hL.1.1⟩ :=
          tau_apply_of_mem_AL_some (i := j) h hD hα hL hH hcomm
        exact (lem92b_classFun_apply_of_isConj (lem92b_isClassFun_tau Lhat n Hs α)
          hcnj').trans h1
      rw [hτ, alphaI1LM_apply]
      rcases eq_or_ne H 1 with hH1 | hH1
      · -- `H = 1`: then `A = L` and `j = i`
        have hcnjL : IsConj (N : X) L := by
          have h0 : A = L := by rw [hAeq, hH1, mul_one]
          rwa [h0] at hcnj
        have hji : j = i := by
          by_contra hne
          obtain ⟨x, hx⟩ := isConj_iff.mp hcnjL
          have h1 : x⁻¹ * L * x⁻¹⁻¹ ∉ hatNp (Hs i) :=
            not_conj_mem_hatNp_of_mem_Lset (i := j) (j := i) h hD (Ne.symm hne) hL (x := x⁻¹)
          rw [inv_inv] at h1
          have h2 : x⁻¹ * L * x = (N : X) := by rw [← hx]; group
          rw [h2] at h1
          exact h1 hN
        have hLi : L ∈ Lset Lhat (Hs i) := hji ▸ hL
        have hL𝔑i : L ∈ Lgrp (Hs i : Set X) := hji ▸ hL𝔑j
        have hLtp : L ∈ hatNp (Hs i) := by
          obtain ⟨x, hx⟩ := isConj_iff.mp hcnjL
          have hx' : x⁻¹ * L * x⁻¹⁻¹ = (N : X) := by rw [← hx]; group
          exact mem_hatNp_of_conj_mem_hatNp_of_mem_Lset h hD hLi hLhat (x := x⁻¹)
            (by rw [hx']; exact hN)
        obtain ⟨x, hx⟩ := isConj_iff.mp hcnjL
        have hxmem : x ∈ Lgrp (Hs i : Set X) := by
          by_contra hnot
          have h1 := hTI.2 x hnot L hLtp
          rw [show x⁻¹ * L * x = (N : X) from by rw [← hx]; group] at h1
          exact h1 hN
        rw [lem92b_alpha_apply_projEC_eq_of_isConj h hD hαc hLtp (x := x) hx hxmem]
        rw [projEC_eq_self (h.supp_inf hD i)
          (⟨(L : X), ⟨hLN, hL𝔑i⟩⟩ : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)))]
        rfl
      · -- `H ≠ 1`: then `j = i` (the bad case is impossible), `A ∈ Ñ_i^#`
        have hji : j = i := by
          by_contra hne
          exact absurd (hAeq ▸ hcnj)
            (lem92b_not_isConj_mul_of_mem_hatNp h hD hne hN hL hH hH1 hcomm)
        have hL𝔑i : L ∈ Lgrp (Hs i : Set X) := hji ▸ hL𝔑j
        have hH𝔑i : H ∈ Lgrp (Hs i : Set X) := hji ▸ hH𝔑j
        have hAKi : L * H ∉ (Hs i : Set X) := hji ▸ hAKj
        have hHi : H ∈ Hs i := hji ▸ hH
        have hA𝔑i : A ∈ Lgrp (Hs i : Set X) := by
          rw [hAeq]
          exact (Lgrp (Hs i : Set X)).mul_mem hL𝔑i hH𝔑i
        have hAtpi : A ∈ hatNp (Hs i) := by
          have h1 : L * H ∈ hatNp (Hs i) :=
            mem_hatNp_iff.mpr ⟨hAeq ▸ hA𝔑i, hAKi, H, hHi, hH1, hAHj⟩
          rw [hAeq]
          exact h1
        obtain ⟨x, hx⟩ := isConj_iff.mp hcnj
        have hxmem : x ∈ Lgrp (Hs i : Set X) := by
          by_contra hnot
          have h1 := hTI.2 x hnot A hAtpi
          rw [show x⁻¹ * A * x = (N : X) from by rw [← hx]; group] at h1
          exact h1 hN
        rw [lem92b_alpha_apply_projEC_eq_of_isConj h hD hαc hAtpi (x := x) hx hxmem]
        have hπA : projEC Lhat (Hs i) ⟨A, hA𝔑i⟩ =
            (⟨(L : X), ⟨hLN, hL𝔑i⟩⟩ : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X))) := by
          have hEq : (⟨A, hA𝔑i⟩ : ↥(Lgrp (Hs i : Set X))) =
              ⟨(L : X), hL𝔑i⟩ * ⟨H, hH𝔑i⟩ := by
            ext
            simp only [Subgroup.coe_mul]
            exact hAeq
          have hstep : projEC Lhat (Hs i) (⟨(L : X), hL𝔑i⟩ * ⟨H, hH𝔑i⟩) =
              (⟨(L : X), ⟨hLN, hL𝔑i⟩⟩ : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X))) := by
            rw [projEC_mul (h.supp_prod hD i) (h.supp_inf hD i) ⟨(L : X), hL𝔑i⟩
              ⟨H, hH𝔑i⟩,
              projEC_eq_self (h.supp_inf hD i) ⟨(L : X), hLN, hL𝔑i⟩]
            rw [projEC_eq_of (h.supp_inf hD i) (m := 1) (by
              rw [Subgroup.coe_one, inv_one, mul_one]; exact hHi), mul_one]
          rw [hEq, hstep]
        rw [hπA]
        rfl
  · -- `N` is not conjugate to `AU`: both sides vanish
    have h1 : tau Lhat n Hs α (N : X) = 0 :=
      tau_eq_zero_of_not_isConj h (Or.inl hD) hα hAU
    have h2 : alphaI1LM Lhat (Hs i) α N = 0 :=
      alphaI1_eq_zero_of_not_inConjAU h (Or.inl hD) hα hAU
    rw [h1, h2]

/-- Feit--Thompson 9.2, second part (pp. 806-807).  Let `Lhat` be tamely imbedded in the finite
group `X` with supporting subgroups `Hs`, with `Dset Lhat` non-empty, let `α` be a class function
of `Lgrp Lhat` in `C0 Lhat` (it vanishes off `Lhat^#` and at `1`), and let `θ` be an irreducible
character of `Norm(Hs i)` which does not contain `Hs i` in its kernel, i.e. whose restriction to
`Hs i` is orthogonal to the principal character.  Then the Dade map `tau` of (9.4) carries `α` to a
function orthogonal to `θ` on `Norm(Hs i)`: `⟪α^tau|_{N_i}, θ⟫ = 0`.

Route: the pointwise identity `tau α N = alphaI1LM α N` for `N` in `Hs i` or in `hatNp (Hs i)`
(9.2 first part), together with FT 4.3 (`irr_vanishes_off_hatN`: `θ` vanishes off
`hatN (Hs i)`) and `cfInner_const_coset_eq_zero` (the inflation `alphaI1LM` of a class function of
`Norm(Hs i)/Hs i` is orthogonal to an irreducible which is not trivial on `Hs i`).  In the case
`N ∈ hatNp (Hs i)`, the first part is obtained from the source's argument: by
`[28] p. 162` (Schur--Zassenhaus in `Hs i * <N>`; the complement is solvable) every element of
`Norm(Hs i)` is conjugate *in* `Norm(Hs i)` to some `A = H * L` with `L` in
`Lgrp Lhat ⊓ Lgrp (Hs i)` and `H` in `Hs i`; `alphaI1LM` is a class function of `Norm(Hs i)`, so
it suffices to know `alphaI1LM alpha A = alpha L` (which is `projEC_eq_of`), and
`tau alpha A = alpha L` is the value part of FT 9.1 (the available
`Work.Tame.tau_apply_of_mem_AL`) as soon as `L` lies in `Lset Lhat (Hs i)`, with `tau alpha A = 0`
and `alpha L = 0` otherwise (`alpha` in `C0` vanishes off `Lhat^#`).

The file `Submission/Work/Tame/tau_res_quotient_v2.lean` contains a nearly complete proof of this
result; read it (do not import it - it does not compile yet).  Its internal helpers are yours to
restate.  The surrounding API is in `ft93_aux.lean`, `tau_apply_of_mem_AL.lean`,
`tau_apply_one.lean`, `irr_vanishes_off_hatN.lean` and `cfInner_tau_theta.lean`.  This result is
the load-bearing input of FT 10.3, so keep the statement exactly as written. -/
theorem lem92b {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} {i : Fin n} (h : IsTamelyImbedded Lhat n Hs)
    (hD : (Dset Lhat).Nonempty) {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat)
    {θ : ↥(Lgrp (Hs i : Set X)) → ℂ} (hθ : θ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)))
    (hθker : Coherence.cfInner
      (fun hh : ↥(Hs i) => θ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩) (1 : ↥(Hs i) → ℂ) = 0) :
    Coherence.cfInner (fun N : ↥(Lgrp (Hs i : Set X)) => tau Lhat n Hs α (N : X)) θ = 0 := by
  classical
  -- `θ` is not trivial on `𝔎_i`
  obtain ⟨H₀, hH₀⟩ := lem92b_exists_mem_apply_ne_one_of_cfInner_eq_zero (K := Hs i) hθ hθker
  -- pointwise: `τ(α)` and `α_{i1}` agree wherever `θ` does not vanish
  have hpt : ∀ N : ↥(Lgrp (Hs i : Set X)),
      (tau Lhat n Hs α (N : X) - alphaI1LM Lhat (Hs i) α N) * starRingEnd ℂ (θ N) = 0 := by
    intro N
    by_cases hθN : θ N = 0
    · rw [hθN, map_zero, mul_zero]
    · have hKbot : Hs i ≠ ⊥ := h.supp_ne_bot hD i
      have hmem : (N : X) ∈ (Hs i : Set X) ∨ (N : X) ∈ hatNp (Hs i) := by
        by_contra hc
        push_neg at hc
        obtain ⟨hcK, hcNp⟩ := hc
        have hcN : (N : X) ∉ hatN (Hs i) := by
          intro hmem'
          have h2 : (N : X) ∈ hatNp (Hs i) ∪ ({1} : Set X) := by
            rw [← hatN_eq_hatNp_union_singleton hKbot]
            exact hmem'
          rcases h2 with h2 | h2
          · exact hcNp h2
          · exact hcK (by rw [h2]; exact (Hs i).one_mem)
        exact hθN (irr_vanishes_off_hatN h hD i hθ ⟨H₀, hH₀⟩ hcN hcK)
      rcases hmem with hmem | hmem
      · rw [lem92b_tau_eq_alphaI1_of_mem_Hs h hD hα hmem, sub_self, zero_mul]
      · rw [lem92b_tau_eq_alphaI1_of_mem_hatNp h hD hα hmem, sub_self, zero_mul]
  -- hence the two inner products agree
  have hsame : Coherence.cfInner
        (fun N : ↥(Lgrp (Hs i : Set X)) => tau Lhat n Hs α (N : X)) θ
      = Coherence.cfInner (alphaI1LM Lhat (Hs i) α) θ := by
    rw [Coherence.cfInner_apply, Coherence.cfInner_apply]
    congr 1
    refine Finset.sum_congr rfl (fun N _ => ?_)
    have hN := hpt N
    rw [sub_mul] at hN
    exact sub_eq_zero.mp hN
  rw [hsame]
  -- `α_{i1}` is constant on the cosets of `𝔎_i`, so it is orthogonal to `θ`
  have hsup : Lgrp (Hs i : Set X) = Hs i ⊔ (Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) :=
    h.supp_prod hD i
  have hinf : Hs i ⊓ Lgrp Lhat = ⊥ := h.supp_inf hD i
  haveI : ((Hs i).subgroupOf (Lgrp (Hs i : Set X))).Normal := Subgroup.normal_in_normalizer
  refine cfInner_const_coset_eq_zero (K := (Hs i).subgroupOf (Lgrp (Hs i : Set X))) hθ
    ⟨⟨(H₀ : X), (Hs i).le_normalizer H₀.2⟩,
      Subgroup.mem_subgroupOf.mpr H₀.2, hH₀⟩ ?_ ?_
  · exact alphaI1_isClassFun hsup hinf hα.1
  · intro n hn g
    have hnK : ((n : ↥(Lgrp (Hs i : Set X))) : X) ∈ Hs i := Subgroup.mem_subgroupOf.mp hn
    have hprojn : projEC Lhat (Hs i) n = 1 :=
      projEC_eq_of (m := 1) hinf (by rw [Subgroup.coe_one, inv_one, mul_one]; exact hnK)
    show alphaI1LM Lhat (Hs i) α (n * g) = alphaI1LM Lhat (Hs i) α g
    rw [alphaI1LM_apply, alphaI1LM_apply, projEC_mul hsup hinf n g, hprojn, one_mul]

end Work.Tame
