import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.card_extraspecial
import Submission.Work.PGroup.center_eq_commutator_of_isExtraspecial
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix VII, Part 2: the value of `χ` on the coset `Q·s`

Let `H = Q ⋊ P` with `Q` extraspecial of order `q ^ (2m+1)`, `P` of prime order `p`, `p ∤ |Q|`,
`C_Q(P) = Z(Q)` and `[P,Q] = Q`.  For `s ∈ P`, `s ≠ 1`, the values `‖χ‖²` of an irreducible
character whose kernel misses `Z(Q)` are constant on the coset `Q s`, equal to `‖χ s‖²`.

The group-theoretic input (`part2_coset_rep_self`) is that every element of `Q` is a central
element times a `Q`-conjugate of `s`:

`∀ u ∈ Q, ∃ z ∈ Z(Q), ∃ t ∈ Q, u = z · (t s t⁻¹ s⁻¹)`.

This is proved by the standard fixed-point-free argument: the map `t ↦ t s t⁻¹ s⁻¹` is a
homomorphism modulo `Z(Q)` (because `[Q,Q] = Z(Q)`, so `Q/Z(Q)` is abelian), its kernel is
`Z(Q)` (if `t s t⁻¹ s⁻¹ ∈ Z(Q)` then iterating `sᵏ t s⁻ᵏ = z⁻ᵏ t` gives `z^p = 1`, and
`z ∈ Z(Q)` has order dividing `q` with `p ≠ q`, so `z = 1`, whence `t ∈ C_Q(s) = Z(Q)`), and a
finite group cannot inject properly into itself: `Q/Z(Q) → Q/Z(Q)` is bijective.
-/

set_option maxHeartbeats 1000000

open scoped commutatorElement

noncomputable section

namespace Work.Hering.AppVII

open Classical

variable {H : Type*} [Group H] [Fintype H]

/-- The centre of the group `↥Q`, as a subset of `H`, is `Q ⊓ C_H(Q)`. -/
theorem mem_center_subtype_iff {Q : Subgroup H} (x : ↥Q) :
    x ∈ Subgroup.center ↥Q ↔ (x : H) ∈ Q ⊓ Subgroup.centralizer (Q : Set H) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨x.2, fun y hy => congrArg Subtype.val (h ⟨y, hy⟩)⟩
  · rintro ⟨-, h⟩ y
    exact Subtype.ext (h (y : H) y.2)

/-- An element of `Q` centralising all of `Q` centralises all of `H` (it centralises `P` by
`Q ⊓ C_H(Q) = Q ⊓ C_H(P)`). -/
theorem part2_coset_mem_center {Q P : Subgroup H} (hQn : Q.Normal) (hsup : P ⊔ Q = ⊤)
    (hcp : Q ⊓ Subgroup.centralizer (P : Set H) = Q ⊓ Subgroup.centralizer (Q : Set H))
    {z : H} (hz : z ∈ Q ⊓ Subgroup.centralizer (Q : Set H)) : z ∈ Subgroup.center H := by
  have hzP : z ∈ Subgroup.centralizer (P : Set H) := by
    have h2 : z ∈ Q ⊓ Subgroup.centralizer (P : Set H) := by rw [hcp]; exact hz
    exact h2.2
  have hzQ : z ∈ Subgroup.centralizer (Q : Set H) := hz.2
  rw [Subgroup.mem_center_iff]
  intro h
  have hmem : h ∈ Q ⊔ P := by rw [sup_comm, hsup]; exact Subgroup.mem_top h
  obtain ⟨q, hq, s', hs', rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := Q) (t := P)).mp hmem
  have h1 : z * q = q * z := (Subgroup.mem_centralizer_iff.mp hzQ q hq).symm
  have h2 : z * s' = s' * z := (Subgroup.mem_centralizer_iff.mp hzP s' hs').symm
  calc q * s' * z = q * (s' * z) := by rw [mul_assoc]
    _ = q * (z * s') := by rw [← h2]
    _ = q * z * s' := by rw [mul_assoc]
    _ = z * q * s' := by rw [← h1]
    _ = z * (q * s') := by rw [mul_assoc]

/-- **Every element of `Q` is a central element times a conjugate of `s`.** -/
theorem part2_coset_rep_self {q p : ℕ} (Q P : Subgroup H) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) (hq : q.Prime)
    (hQext : Work.PGroup.IsExtraspecial q Q) (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hpQ : ¬ p ∣ Nat.card Q)
    (hcp : Q ⊓ Subgroup.centralizer (P : Set H) = Q ⊓ Subgroup.centralizer (Q : Set H))
    {s : ↥P} (hs : s ≠ 1) (u : ↥Q) :
    ∃ z : H, z ∈ Q ⊓ Subgroup.centralizer (Q : Set H) ∧ ∃ t : ↥Q,
      (u : H) = z * ((t : H) * (s : H) * (t : H)⁻¹ * (s : H)⁻¹) := by
  classical
  -- ## Step 0: `q ∣ |Q|`, `p ≠ q`, `P = ⟨s⟩`, `s ^ p = 1`
  have hZc_card : Nat.card (Subgroup.center ↥Q) = q := Work.PGroup.card_center_subtype Q hQext
  have hq_dvd : q ∣ Nat.card ↥Q := by
    rw [← hZc_card]; exact Subgroup.card_subgroup_dvd_card _
  have hpq : p ≠ q := fun h => hpQ (h ▸ hq_dvd)
  have hsne : (s : H) ≠ 1 := fun h => hs (Subtype.ext h)
  have hs_pow : (s : H) ^ p = 1 := by
    have h1 : (s : ↥P) ^ p = 1 := by
      rw [← hPcard]; exact pow_card_eq_one'
    simpa using congrArg (fun x : ↥P => (x : H)) h1
  have hord : orderOf (s : H) = p := by
    have h1 : orderOf (s : H) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hs_pow
    rcases hp.eq_one_or_self_of_dvd _ h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hsne
    · exact h
  have hPz : P = Subgroup.zpowers (s : H) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr s.2) ?_).symm
    rw [Nat.card_zpowers, hord]
    exact le_of_eq hPcard
  have hcent : Subgroup.centralizer (P : Set H) = Subgroup.centralizer ({(s : H)} : Set H) := by
    conv_lhs => rw [hPz]
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_closure ({(s : H)} : Set H)
  have hZ_s : ∀ z : H, z ∈ Q ⊓ Subgroup.centralizer (Q : Set H) → z * (s : H) = (s : H) * z := by
    intro z hz
    have hzP : z ∈ Subgroup.centralizer (P : Set H) := by
      have h2 : z ∈ Q ⊓ Subgroup.centralizer (P : Set H) := by rw [hcp]; exact hz
      exact h2.2
    have hzP' : z ∈ Subgroup.centralizer ({(s : H)} : Set H) := by rw [← hcent]; exact hzP
    exact (Subgroup.mem_centralizer_iff.mp hzP' (s : H) (Set.mem_singleton _)).symm
  -- ## Step 1: the map `Φ t = t s t⁻¹ s⁻¹`
  have hΦmem : ∀ t : ↥Q, (t : H) * (s : H) * (t : H)⁻¹ * (s : H)⁻¹ ∈ Q := by
    intro t
    have h1 : (s : H) * (t : H)⁻¹ * (s : H)⁻¹ ∈ Q :=
      hQn.conj_mem (t : H)⁻¹ (Q.inv_mem t.2) (s : H)
    simpa [mul_assoc] using mul_mem t.2 h1
  let Φ : ↥Q → ↥Q := fun t => ⟨(t : H) * (s : H) * (t : H)⁻¹ * (s : H)⁻¹, hΦmem t⟩
  have hΦ_coe : ∀ t : ↥Q, ((Φ t : ↥Q) : H) = (t : H) * (s : H) * (t : H)⁻¹ * (s : H)⁻¹ :=
    fun t => rfl
  -- ## Step 2: `Q` has class two
  have hcomm_le : ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ ≤ Subgroup.center ↥Q := by
    rw [Work.PGroup.center_subtype_eq_commutator Q hQext]
  -- ## Step 3: `Φ` is multiplicative modulo the centre
  have hXmem : ∀ t : ↥Q, (s : H) * (t : H) * (s : H)⁻¹ ∈ Q := fun t =>
    hQn.conj_mem (t : H) t.2 (s : H)
  have hconj1 : ∀ t₁ t₂ : ↥Q,
      Φ (t₁ * t₂) * (Φ t₁ * Φ t₂)⁻¹
        = ⁅(⟨(s : H) * (t₁ : H) * (s : H)⁻¹, hXmem t₁⟩ : ↥Q), Φ t₂⁆ := by
    intro t₁ t₂
    have hmem : ⁅(⟨(s : H) * (t₁ : H) * (s : H)⁻¹, hXmem t₁⟩ : ↥Q), Φ t₂⁆
        ∈ Subgroup.center ↥Q :=
      (Subgroup.commutator_le.mp hcomm_le) _ (Subgroup.mem_top _) _ (Subgroup.mem_top _)
    calc Φ (t₁ * t₂) * (Φ t₁ * Φ t₂)⁻¹
        = Φ t₁ * ⁅(⟨(s : H) * (t₁ : H) * (s : H)⁻¹, hXmem t₁⟩ : ↥Q), Φ t₂⁆ * (Φ t₁)⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hΦ_coe, commutatorElement_def]
          group
      _ = ⁅(⟨(s : H) * (t₁ : H) * (s : H)⁻¹, hXmem t₁⟩ : ↥Q), Φ t₂⁆ := by
          rw [Subgroup.mem_center_iff.mp hmem (Φ t₁)]
          group
  have hΨmul : ∀ t₁ t₂ : ↥Q,
      QuotientGroup.mk' (Subgroup.center ↥Q) (Φ (t₁ * t₂))
        = QuotientGroup.mk' (Subgroup.center ↥Q) (Φ t₁)
          * QuotientGroup.mk' (Subgroup.center ↥Q) (Φ t₂) := by
    intro t₁ t₂
    rw [← map_mul]
    rw [QuotientGroup.mk'_eq_mk']
    have hmem : ⁅(⟨(s : H) * (t₁ : H) * (s : H)⁻¹, hXmem t₁⟩ : ↥Q), Φ t₂⁆
        ∈ Subgroup.center ↥Q :=
      (Subgroup.commutator_le.mp hcomm_le) _ (Subgroup.mem_top _) _ (Subgroup.mem_top _)
    have hmem' : (⁅(⟨(s : H) * (t₁ : H) * (s : H)⁻¹, hXmem t₁⟩ : ↥Q), Φ t₂⁆)⁻¹
        ∈ Subgroup.center ↥Q := (Subgroup.center ↥Q).inv_mem hmem
    have hc := hconj1 t₁ t₂
    refine ⟨(Φ (t₁ * t₂))⁻¹ * (Φ t₁ * Φ t₂), ?_, by group⟩
    have hA : Φ (t₁ * t₂)
        = ⁅(⟨(s : H) * (t₁ : H) * (s : H)⁻¹, hXmem t₁⟩ : ↥Q), Φ t₂⁆ * (Φ t₁ * Φ t₂) := by
      rw [← hc]
      group
    have hz : (Φ (t₁ * t₂))⁻¹ * (Φ t₁ * Φ t₂)
        = (⁅(⟨(s : H) * (t₁ : H) * (s : H)⁻¹, hXmem t₁⟩ : ↥Q), Φ t₂⁆)⁻¹ := by
      rw [hA, mul_inv_rev, Subgroup.mem_center_iff.mp hmem' ((Φ t₁ * Φ t₂)⁻¹)]
      group
    rw [hz]
    exact hmem'
  -- ## Step 4: the kernel is the centre
  have hker : ∀ t : ↥Q, Φ t ∈ Subgroup.center ↥Q ↔ t ∈ Subgroup.center ↥Q := by
    intro t
    constructor
    · intro ht
      -- `z := Φ t` is central, `s t = z⁻¹ t s`, and iterating gives `z ^ p = 1`
      have hzQ : (Φ t : H) ∈ Q ⊓ Subgroup.centralizer (Q : Set H) :=
        (mem_center_subtype_iff (Φ t)).mp ht
      have hz_center : (Φ t : H) ∈ Subgroup.center H :=
        part2_coset_mem_center hQn hsup hcp hzQ
      have hst : (s : H) * (t : H) = (Φ t : H)⁻¹ * (t : H) * (s : H) := by
        have h1 : (Φ t : H) * ((s : H) * (t : H)) = (t : H) * (s : H) := by
          rw [hΦ_coe t]; group
        have h2 := congrArg (fun w => (Φ t : H)⁻¹ * w) h1
        simpa [mul_assoc] using h2
      have hzpow_comm : ∀ k : ℕ, ∀ x : H, x * ((Φ t : H)⁻¹) ^ k = ((Φ t : H)⁻¹) ^ k * x := by
        intro k x
        have h1 : (Φ t : H)⁻¹ ∈ Subgroup.center H := (Subgroup.center H).inv_mem hz_center
        have h2 : ((Φ t : H)⁻¹) ^ k ∈ Subgroup.center H := (Subgroup.center H).pow_mem h1 k
        exact Subgroup.mem_center_iff.mp h2 x
      have hiter : ∀ k : ℕ,
          (s : H) ^ k * (t : H) = ((Φ t : H)⁻¹) ^ k * (t : H) * (s : H) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc (s : H) ^ (k + 1) * (t : H)
              = (s : H) * ((s : H) ^ k * (t : H)) := by rw [pow_succ']; group
            _ = (s : H) * (((Φ t : H)⁻¹) ^ k * (t : H) * (s : H) ^ k) := by rw [ih]
            _ = (s : H) * ((Φ t : H)⁻¹) ^ k * (t : H) * (s : H) ^ k := by group
            _ = ((Φ t : H)⁻¹) ^ k * (s : H) * (t : H) * (s : H) ^ k := by
                  rw [hzpow_comm k (s : H)]
            _ = ((Φ t : H)⁻¹) ^ k * ((s : H) * (t : H)) * (s : H) ^ k := by group
            _ = ((Φ t : H)⁻¹) ^ k * ((Φ t : H)⁻¹ * (t : H) * (s : H)) * (s : H) ^ k := by
                  rw [hst]
            _ = ((Φ t : H)⁻¹) ^ (k + 1) * (t : H) * (s : H) ^ (k + 1) := by
                  rw [pow_succ', pow_succ']; group
      have hzp : ((Φ t : H)⁻¹) ^ p = 1 := by
        have h1 := hiter p
        rw [hs_pow, one_mul, mul_one] at h1
        have h2 := congrArg (fun w => w * (t : H)⁻¹) h1
        simpa using h2.symm
      have hzp' : (Φ t : ↥Q) ^ p = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one, hΦ_coe]
        have h3 : ((Φ t : H) ^ p)⁻¹ = 1 := by rw [← inv_pow, hzp]
        exact inv_eq_one.mp h3
      have hz1 : (Φ t : ↥Q) = 1 := by
        have h1 : orderOf (Φ t : ↥Q) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp'
        have h2 : orderOf (Φ t : ↥Q) ∣ q := by
          have h3 : orderOf (⟨Φ t, ht⟩ : ↥(Subgroup.center ↥Q))
              ∣ Nat.card ↥(Subgroup.center ↥Q) := orderOf_dvd_natCard _
          have h4 : orderOf (⟨Φ t, ht⟩ : ↥(Subgroup.center ↥Q)) = orderOf (Φ t : ↥Q) :=
            (Subgroup.orderOf_coe _).symm
          rw [h4, hZc_card] at h3
          exact h3
        rcases hp.eq_one_or_self_of_dvd _ h1 with h | h
        · exact orderOf_eq_one_iff.mp h
        · exfalso
          rw [h] at h2
          rcases hq.eq_one_or_self_of_dvd p h2 with h3 | h3
          · exact hp.ne_one h3
          · exact hpq h3
      -- hence `t` commutes with `s`
      have hts : (t : H) * (s : H) = (s : H) * (t : H) := by
        have h := congrArg (fun x : ↥Q => (x : H)) hz1
        rw [hΦ_coe, Subgroup.coe_one] at h
        have h2 : (t : H) * (s : H)
            = ((t : H) * (s : H) * (t : H)⁻¹ * (s : H)⁻¹) * ((s : H) * (t : H)) := by
          group
        rw [h2, h, one_mul]
      have htP : (t : H) ∈ Subgroup.centralizer (P : Set H) := by
        rw [hcent]
        exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hts.symm)
      have h2 : (t : H) ∈ Q ⊓ Subgroup.centralizer (P : Set H) := ⟨t.2, htP⟩
      rw [hcp] at h2
      exact (mem_center_subtype_iff t).mpr h2
    · intro ht
      have hΦ1 : Φ t = 1 := by
        apply Subtype.ext
        rw [hΦ_coe, Subgroup.coe_one]
        have h2 : (t : H) ∈ Q ⊓ Subgroup.centralizer (Q : Set H) :=
          (mem_center_subtype_iff t).mp ht
        have hts : (t : H) * (s : H) = (s : H) * (t : H) := hZ_s _ h2
        rw [hts]
        group
      rw [hΦ1]
      exact Subgroup.one_mem _
  -- ## Step 5: surjectivity of `t ↦ Φ t` modulo the centre
  have hsurj : ∀ v : ↥Q ⧸ Subgroup.center ↥Q, ∃ t : ↥Q,
      QuotientGroup.mk' (Subgroup.center ↥Q) (Φ t) = v := by
    let Ψ : ↥Q →* ↥Q ⧸ Subgroup.center ↥Q :=
      { toFun := fun t => QuotientGroup.mk' (Subgroup.center ↥Q) (Φ t)
        map_one' := by
          have h1 : Φ (1 : ↥Q) = 1 := by
            apply Subtype.ext
            rw [hΦ_coe, Subgroup.coe_one]
            simp
          rw [h1]
          exact map_one _
        map_mul' := hΨmul }
    have hkerΨ : Ψ.ker = Subgroup.center ↥Q := by
      ext t
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' (Subgroup.center ↥Q) (Φ t) : ↥Q ⧸ Subgroup.center ↥Q) = 1
        ↔ t ∈ Subgroup.center ↥Q
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hker t
    have htop : Ψ.range = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      have h1 : Nat.card Ψ.ker * Nat.card Ψ.range = Nat.card ↥Q := by
        rw [← Subgroup.card_mul_index Ψ.ker, Subgroup.index_ker]
      rw [hkerΨ, hZc_card] at h1
      have h2 : Nat.card (↥Q ⧸ Subgroup.center ↥Q) * Nat.card (Subgroup.center ↥Q)
          = Nat.card ↥Q := (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
      rw [hZc_card] at h2
      have h3 : q * Nat.card Ψ.range = q * Nat.card (↥Q ⧸ Subgroup.center ↥Q) := by
        rw [h1, ← h2, Nat.mul_comm]
      exact Nat.mul_left_cancel hq.pos h3
    intro v
    have hv : v ∈ Ψ.range := htop ▸ Subgroup.mem_top v
    obtain ⟨t, ht⟩ := hv
    exact ⟨t, ht⟩
  -- ## Step 6: conclusion
  obtain ⟨t, ht⟩ := hsurj (QuotientGroup.mk' (Subgroup.center ↥Q) u)
  obtain ⟨w, hw, hwt⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center ↥Q)).mp ht
  have h1 : (u : ↥Q) = w * Φ t := by
    rw [← hwt, Subgroup.mem_center_iff.mp hw (Φ t)]
  refine ⟨(w : H), (mem_center_subtype_iff w).mp hw, t, ?_⟩
  have h2 : ((u : ↥Q) : H) = (w : H) * ((Φ t : ↥Q) : H) := congrArg Subtype.val h1
  rw [hΦ_coe t] at h2
  exact h2

/-- **The value of `‖χ‖²` on a coset of `Q`.** -/
theorem part2_coset_value_self {q p : ℕ} (Q P : Subgroup H) [Fintype ↥P]
    (hQn : Q.Normal) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) (hq : q.Prime)
    (hQext : Work.PGroup.IsExtraspecial q Q) (hp : p.Prime) (hPcard : Nat.card P = p)
    (hpQ : ¬ p ∣ Nat.card Q)
    (hcp : Q ⊓ Subgroup.centralizer (P : Set H) = Q ⊓ Subgroup.centralizer (Q : Set H))
    {χ : H → ℂ} (hχ : χ ∈ Work.CharCore.Irr H)
    (hscalar : ∀ z : H, z ∈ Q ⊓ Subgroup.centralizer (Q : Set H) →
      ∃ ω : ℂ, ω * starRingEnd ℂ ω = 1 ∧ ∀ x : H, χ (z * x) = ω * χ x)
    {s : ↥P} (hs : s ≠ 1) (u : ↥Q) :
    Complex.normSq (χ ((u : H) * (s : H))) = Complex.normSq (χ (s : H)) := by
  obtain ⟨z, hz, t, ht⟩ :=
    part2_coset_rep_self Q P hQn hinf hsup hq hQext hp hPcard hpQ hcp hs u
  obtain ⟨ω, hω, hωχ⟩ := hscalar z hz
  have hus : (u : H) * (s : H) = z * ((t : H) * (s : H) * (t : H)⁻¹) := by
    rw [ht]; group
  have hclass := Work.CharCore.isClassFun_of_mem_Irr hχ
  have hval : χ ((u : H) * (s : H)) = ω * χ (s : H) := by
    rw [hus, hωχ ((t : H) * (s : H) * (t : H)⁻¹), hclass (s : H) (t : H)]
  have hωns : Complex.normSq ω = 1 := by
    have h := Complex.mul_conj ω
    have h1 : ((Complex.normSq ω : ℝ) : ℂ) = 1 := by rw [← h, hω]
    simpa using h1
  rw [hval, Complex.normSq_mul, hωns, one_mul]

end Work.Hering.AppVII
