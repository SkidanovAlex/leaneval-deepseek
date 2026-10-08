import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmG.resFun_indFun_eq_of_vanishes_off_hall`

Restriction/induction identity on a Hall-decomposed subgroup: if `H = Q ⋊ D` is a Hall
decomposition (`Q ⊔ D = H`, `Q ⊓ D = ⊥`, coprime orders), `Q` is normalised by `H` and is a
TI subgroup of `G` relative to `H` (`Q ∩ Qˣ = ⊥` for `x ∉ H`), and `μ` is a class function on
`H` with `μ 1 = 0` vanishing off `Q`, then `Res_H^G (Ind_H^G μ) = μ`.

The proof is the explicit pointwise computation of the defining sum of `Ind_H^G μ`.  For
`h ∈ H`, the defining sum `∑_{x : x h x⁻¹ ∈ H} μ (x h x⁻¹)` is split into the terms with
`x ∈ H` (each equal to `μ h`, since `μ` is a class function) and the terms with `x ∉ H`.
The latter vanish because of `conj_eq_one_of_mem_of_hall_aux`: if `x ∉ H` and `x h x⁻¹ ∈ Q`,
then `x h x⁻¹ = 1` — the Hall/coprime structure plus TI force this.
-/

set_option autoImplicit false

noncomputable section

open Classical
open scoped Pointwise

namespace Work.ThmG

/-- For `x ∈ S` in a finite subgroup, `x ^ Nat.card S = 1` (Lagrange). -/
private theorem pow_natCard_eq_one_of_mem {G : Type*} [Group G] [Fintype G] {S : Subgroup G}
    {x : G} (hx : x ∈ S) : x ^ Nat.card S = 1 := by
  classical
  have h : (⟨x, hx⟩ : S) ^ Fintype.card S = 1 := pow_card_eq_one
  have h2 := congrArg (Subtype.val) h
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
  rwa [Nat.card_eq_fintype_card]

/-- **Hall decomposition power lemma.**  If `Q ⊔ D = H`, `H` normalises `Q`, and `h ∈ H`, then
`h ^ Nat.card D ∈ Q`: writing `h = q * d` with `q ∈ Q`, `d ∈ D`, the binomial-style identity
`(q * d) ^ n = c_n * d ^ n` with `c_n ∈ Q` (using that `d` normalises `Q`) gives
`h ^ Nat.card D = c * d ^ Nat.card D = c ∈ Q`. -/
private theorem pow_natCard_mem_of_mem_of_sup_eq {G : Type*} [Group G] [Fintype G]
    {H Q D : Subgroup G} (hsup : Q ⊔ D = H)
    (hQn : H ≤ Subgroup.normalizer (Q : Set G)) (h : H) :
    (h : G) ^ Nat.card D ∈ Q := by
  classical
  have hDH : D ≤ H := le_trans le_sup_right (le_of_eq hsup)
  have hDn : D ≤ Subgroup.normalizer (Q : Set G) := le_trans hDH hQn
  -- `H = Q * D`, so `h = q * d`.
  have hmem : (h : G) ∈ (Q : Set G) * (D : Set G) := by
    have h1 : (h : G) ∈ (↑(Q ⊔ D) : Set G) := by rw [hsup]; exact h.2
    rwa [Subgroup.coe_mul_of_right_le_normalizer_left Q D hDn] at h1
  obtain ⟨q, hqQ, d, hdD, hqd⟩ := Set.mem_mul.mp hmem
  -- `(q * d) ^ n = c_n * d ^ n` with `c_n ∈ Q`.
  have key : ∀ n : ℕ, ∃ c ∈ Q, (h : G) ^ n = c * d ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, Q.one_mem, by simp⟩
    | succ n ih =>
        obtain ⟨c, hcQ, hc⟩ := ih
        refine ⟨c * (d ^ n * q * (d ^ n)⁻¹), Q.mul_mem hcQ ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (pow_mem (hDn hdD) n) q).mp hqQ
        · rw [pow_succ, pow_succ, hc, ← hqd]
          group
  obtain ⟨c, hcQ, hc⟩ := key (Nat.card D)
  have hd1 : d ^ Nat.card D = 1 := pow_natCard_eq_one_of_mem hdD
  rw [hc, hd1, mul_one]
  exact hcQ

/-- **The Hall/coprime vanishing step.**  With `H = Q ⋊ D` a Hall decomposition (`Q ⊔ D = H`,
`Q ⊓ D = ⊥`, coprime orders), `H` normalising `Q`, and `Q` a TI subgroup relative to `H`, if
`x ∉ H`, `h ∈ H` and `x * h * x⁻¹ ∈ Q` then `x * h * x⁻¹ = 1`.

Indeed `h = x⁻¹ (x h x⁻¹) x`, so `h ^ |D| ∈ Q` (Hall decomposition) and `h ^ |D| ∈ x⁻¹ Q x`;
TI gives `h ^ |D| = 1`, whence `orderOf h ∣ |D|`; on the other hand `h ^ |Q| = 1`, so
`orderOf h ∣ |Q|`; coprimality gives `h = 1`. -/
private theorem conj_eq_one_of_mem_of_hall_aux {G : Type*} [Group G] [Fintype G]
    {H Q D : Subgroup G} (hsup : Q ⊔ D = H) (hinf : Q ⊓ D = ⊥)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hQn : H ≤ Subgroup.normalizer (Q : Set G))
    (hTI : ∀ x : G, x ∉ H → Q ⊓ Submission.Blueprint.conj x Q = ⊥)
    {x : G} (hx : x ∉ H) {h : H} (hhQ : x * (h : G) * x⁻¹ ∈ Q) :
    x * (h : G) * x⁻¹ = 1 := by
  classical
  have hpowD : (h : G) ^ Nat.card D ∈ Q := pow_natCard_mem_of_mem_of_sup_eq hsup hQn h
  have hxinv : x⁻¹ ∉ H := fun hm => hx (by simpa using H.inv_mem hm)
  -- `h ^ |D| = x⁻¹ * (x h x⁻¹) ^ |D| * x ∈ x⁻¹ Q x`.
  have hmem_conj : (h : G) ^ Nat.card D ∈ Submission.Blueprint.conj x⁻¹ Q := by
    refine Subgroup.mem_map.mpr ⟨(x * (h : G) * x⁻¹) ^ Nat.card D, pow_mem hhQ _, ?_⟩
    show (MulAut.conj x⁻¹) ((x * (h : G) * x⁻¹) ^ Nat.card D) = (h : G) ^ Nat.card D
    rw [map_pow]
    congr 1
    rw [MulAut.conj_apply]
    group
  have hbot : (h : G) ^ Nat.card D ∈ Q ⊓ Submission.Blueprint.conj x⁻¹ Q :=
    ⟨hpowD, hmem_conj⟩
  rw [hTI x⁻¹ hxinv, Subgroup.mem_bot] at hbot
  have hdvdD : orderOf (h : G) ∣ Nat.card D := orderOf_dvd_iff_pow_eq_one.mpr hbot
  -- `h ^ |Q| = x⁻¹ * (x h x⁻¹) ^ |Q| * x = 1`.
  have hq'pow : (x * (h : G) * x⁻¹) ^ Nat.card Q = 1 := pow_natCard_eq_one_of_mem hhQ
  have hpowQ1 : (h : G) ^ Nat.card Q = 1 := by
    have heq : (h : G) = x⁻¹ * (x * (h : G) * x⁻¹) * x := by group
    rw [heq]
    rw [show x⁻¹ * (x * (h : G) * x⁻¹) * x = x⁻¹ * (x * (h : G) * x⁻¹) * (x⁻¹)⁻¹
      by group]
    rw [conj_pow, hq'pow]
    group
  have hdvdQ : orderOf (h : G) ∣ Nat.card Q := orderOf_dvd_iff_pow_eq_one.mpr hpowQ1
  have horder1 : orderOf (h : G) = 1 := by
    have hg : orderOf (h : G) ∣ Nat.gcd (Nat.card D) (Nat.card Q) := Nat.dvd_gcd hdvdD hdvdQ
    rw [hcop.gcd_eq_one] at hg
    exact Nat.dvd_one.mp hg
  have hh1 : (h : G) = 1 := orderOf_eq_one_iff.mp horder1
  rw [hh1]
  group

theorem resFun_indFun_eq_of_vanishes_off_hall {G : Type*} [Group G] [Fintype G]
    {H Q D : Subgroup G} (hsup : Q ⊔ D = H) (hinf : Q ⊓ D = ⊥)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Q))
    (hQn : H ≤ Subgroup.normalizer (Q : Set G))
    (hTI : ∀ x : G, x ∉ H → Q ⊓ Submission.Blueprint.conj x Q = ⊥)
    (μ : H → ℂ) (hμ : Work.CharCore.IsClassFun μ)
    (hμ1 : μ 1 = 0) (hμ0 : ∀ h : H, (h : G) ∉ Q → μ h = 0) :
    Work.Induction.resFun H (Work.Induction.indFun H μ) = μ := by
  classical
  funext h
  rw [Work.Induction.resFun_apply, Work.Induction.indFun_apply_def]
  -- The pointwise comparison of the defining sum.
  have hkey : ∀ x : G,
      (dite (x * (h : G) * x⁻¹ ∈ H) (fun hx => μ ⟨x * (h : G) * x⁻¹, hx⟩)
        (fun _ => 0)) = if x ∈ H then μ h else 0 := by
    intro x
    by_cases hxH : x ∈ H
    · have hmemH : x * (h : G) * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH h.2) (H.inv_mem hxH)
      rw [dite_eq_left hmemH, if_pos hxH]
      have heq : (⟨x * (h : G) * x⁻¹, hmemH⟩ : H) = ⟨x, hxH⟩ * h * ⟨x, hxH⟩⁻¹ := by
        ext
        simp [mul_assoc]
      rw [heq, hμ h ⟨x, hxH⟩]
    · rw [if_neg hxH]
      by_cases hmemH : x * (h : G) * x⁻¹ ∈ H
      · rw [dite_eq_left hmemH]
        by_cases hxQ : x * (h : G) * x⁻¹ ∈ Q
        · have h1 := conj_eq_one_of_mem_of_hall_aux hsup hinf hcop hQn hTI hxH hxQ
          have h2 : (⟨x * (h : G) * x⁻¹, hmemH⟩ : H) = 1 := Subtype.ext (by simpa using h1)
          rw [h2, hμ1]
        · exact hμ0 ⟨x * (h : G) * x⁻¹, hmemH⟩ hxQ
      · rw [dite_eq_right hmemH]
  rw [Finset.sum_congr rfl (fun x _ => hkey x)]
  -- The remaining sum is a constant sum over `H`: it equals `|H| * μ h`.
  have hsum : (∑ x : G, (if x ∈ H then μ h else 0)) = (Nat.card H : ℂ) * μ h := by
    rw [← Finset.sum_filter (s := Finset.univ) (p := fun x : G => x ∈ H)
      (f := fun _ : G => μ h)]
    have hsub : (∑ x ∈ Finset.univ.filter (fun x : G => x ∈ H), (fun _ : G => μ h) x)
        = ∑ x : H, μ h :=
      Finset.sum_subtype (Finset.univ.filter (fun x : G => x ∈ H)) (fun x => by simp)
        (fun _ => μ h)
    rw [hsub]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hsum, ← mul_assoc]
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  rw [inv_mul_cancel₀ hcard, one_mul]

end Work.ThmG
