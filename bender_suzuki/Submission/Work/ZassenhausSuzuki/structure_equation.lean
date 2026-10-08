import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ThmF.ChV12.structureIdentity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.structure_equation`

The structure equation of the split rank-one Zassenhaus configuration (Suzuki 1962 Prop. 9,
HB III 10.6): in a configuration whose root group `Q` has exponent `4` and only central
involutions, there is `g ∈ Q` with `g²` a non-trivial central involution and

`t · g² · t = g · t · g⁻¹`.

The proof follows the (elementary) route through the structure identity
`Work.ThmF.ChV12.structureIdentity` (Peterfalvi II Ch. V §2 Lemma 1 b): the unique pair
`(σ, ρ)` with `σ ∈ Q` an involution, `ρ ∈ Q` and `t σ t⁻¹ = ρ t ρ⁻¹`.  Writing `π = σ t`
one has

* `ρ π ρ⁻¹ = π²` (because `σ` is central in `Q`), so `ρ⁴ = 1` gives `π ^ 15 = 1`;
* `π ≠ 1` and `3 ∤ |G|` force `orderOf π = 5`;
* the uniqueness of the structure pair gives `C_Q(t) = 1`;
* consequently the only involutions `y ∈ Q` with `y π y⁻¹ ∈ ⟨π⟩` are `1` and `σ`
  (the conjugation action of such a `y` permutes `⟨π⟩ ≅ C₅`, so `y π y⁻¹ = π^{±1}`;
  `π` gives `y ∈ C_Q(t) = 1`, `π⁻¹` gives `yσ ∈ C_Q(t) = 1`, i.e. `y = σ`);
* applying this to `y = ρ²` (an involution of `Q` since `ρ⁴ = 1`, with
  `ρ² π ρ⁻² = π⁴`) gives `ρ² = σ`, and `g = ρ` is the required element.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- Conjugation is multiplicative: `(g x g⁻¹) ^ n = g x ^ n g⁻¹`. -/
private lemma conj_pow' (g x : G) (n : ℕ) : (g * x * g⁻¹) ^ n = g * x ^ n * g⁻¹ := by
  rw [← MulAut.conj_apply g x, ← map_pow, MulAut.conj_apply g (x ^ n)]

/-- **`C_Q(t) = 1`** in a split rank-one configuration.  This is the uniqueness part of
Peterfalvi II Ch. V §2 Lemma 1 b) applied to the canonical form: if `y ∈ Q` commutes with
`t`, then `(σ, ρ y)` is again a pair of the structure identity, whence `ρ y = ρ`. -/
private lemma centralizer_Q_t_eq_one (hsplit : IsSplitRankOne H Q t) :
    ∀ y : Q, (y : G) * t * (y : G)⁻¹ = t → y = 1 := by
  intro y hy
  obtain ⟨p, hp, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)
  obtain ⟨σ, ρ⟩ := p
  obtain ⟨hσQ₀, hσord₀, hρQ₀, hσρrel₀⟩ := hp
  have hσQ : σ ∈ Q := hσQ₀
  have hσord : orderOf σ = 2 := hσord₀
  have hρQ : ρ ∈ Q := hρQ₀
  have hσρrel : t * σ * t⁻¹ = ρ * t * ρ⁻¹ := hσρrel₀
  have hγ : (((⟨ρ, hρQ⟩ : Q) * y : Q) : G) * t * (((((⟨ρ, hρQ⟩ : Q) * y : Q))⁻¹ : Q) : G)
      = t * σ * t⁻¹ := by
    calc (((⟨ρ, hρQ⟩ : Q) * y : Q) : G) * t * (((((⟨ρ, hρQ⟩ : Q) * y : Q))⁻¹ : Q) : G)
        = (ρ : G) * ((y : G) * t * (y : G)⁻¹) * (ρ : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
          group
      _ = (ρ : G) * t * (ρ : G)⁻¹ := by rw [hy]
      _ = t * σ * t⁻¹ := hσρrel.symm
  have hpair : (σ, (((⟨ρ, hρQ⟩ : Q) * y : Q) : G)) = (σ, ρ) :=
    huniq (σ, (((⟨ρ, hρQ⟩ : Q) * y : Q) : G)) ⟨hσQ, hσord, (⟨ρ, hρQ⟩ * y).2, hγ.symm⟩
  have hzy : ((⟨ρ, hρQ⟩ : Q) * y : Q) = ⟨ρ, hρQ⟩ :=
    Subtype.ext (congrArg (fun q : G × G => q.2) hpair)
  have hG : (ρ : G) * (y : G) = (ρ : G) := by
    have h' := congrArg (fun z : Q => (z : G)) hzy
    simpa using h'
  refine Subtype.ext ?_
  have h1 : (y : G) = ((1 : Q) : G) := by
    rw [← mul_left_cancel_iff (a := (ρ : G))]
    simpa using hG
  exact h1

/-- **The structure equation of the rank-one configuration (Suzuki 1962 Prop. 9 = HB III 10.6 +
10.7b).**  In a split rank-one Zassenhaus configuration whose root group `Q` has exponent `4`
and only central involutions, there is `g ∈ Q` with `g²` a non-trivial central involution and

`t · g² · t = g · t · g⁻¹`   (i.e. `FRel H t (g²) (g⁻¹)` with witness `m = g`).

Route (elementary, no character theory): HB III Lemma 10.6 (a)–(d) + the exclusion of
`ord g = 2` by `3 ∤ |G|`.  (a): `Q` is regular on `Ω \ {∞}`, so there is `g ∈ Q` with
`sjs = g s g⁻¹` for `j = sᵍˢ`; (b) uniqueness of `(j,g)`; (c) `g j s g⁻¹ = (js)²`;
(d) `j` is a power of `g`, by the `N_𝔪(⟨js⟩) ∩ 𝔪`-is-cyclic argument.  If `ord g = 2` then
`j = g` and the equation gives `(tg)³ = 1`, contradicting `3 ∤ |G|` (note `3 ∤ |G|` holds in
the intended application, where `|G| = (q²+1)q²(q-1)` with `q = 2^m`, `m` odd); so `ord g = 4`
and `j = g²`. -/
theorem structure_equation {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hexp4 : ∀ x : Q, x ^ 4 = 1)
    (hcentral : ∀ x : Q, x * x = 1 → x ∈ Subgroup.center Q)
    (h3 : ¬ 3 ∣ Nat.card G) :
    ∃ g : Q, g ^ 2 ∈ Subgroup.center Q ∧ g ^ 2 ≠ 1 ∧
      t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G) := by
  classical
  -- the structure identity
  obtain ⟨p, hp, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)
  obtain ⟨σ, ρ⟩ := p
  obtain ⟨hσQ₀, hσord₀, hρQ₀, hσρrel₀⟩ := hp
  have hσQ : σ ∈ Q := hσQ₀
  have hσord : orderOf σ = 2 := hσord₀
  have hρQ : ρ ∈ Q := hρQ₀
  have hσρrel : t * σ * t⁻¹ = ρ * t * ρ⁻¹ := hσρrel₀
  have ht2 : t * t = 1 := by
    have hh := pow_orderOf_eq_one t
    rw [hsplit.invol] at hh
    simpa [pow_two] using hh
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- `σ` is a non-trivial central involution of `Q`
  have hσne : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσord
    exact absurd hσord (by norm_num)
  have hσ2 : σ * σ = 1 := by
    have h' := pow_orderOf_eq_one σ
    rw [hσord] at h'
    simpa [pow_two] using h'
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσcent : (⟨σ, hσQ⟩ : Q) ∈ Subgroup.center Q :=
    hcentral ⟨σ, hσQ⟩ (by
      show (⟨σ, hσQ⟩ : Q) * ⟨σ, hσQ⟩ = 1
      exact Subtype.ext (by simpa using hσ2))
  have hσcomm : ∀ z : Q, (z : G) * σ = σ * (z : G) := by
    intro z
    have h := (Subgroup.mem_center_iff.mp hσcent) z
    exact congrArg (fun w : Q => (w : G)) h
  -- `ρ⁴ = 1`
  have hρ4 : ρ ^ 4 = 1 := by
    have h' := hexp4 ⟨ρ, hρQ⟩
    simpa using congrArg (fun z : Q => (z : G)) h'
  -- `π = σ t`, and `ρ π ρ⁻¹ = π²`
  set π : G := σ * t with hπdef
  have hconjρ : ρ * π * ρ⁻¹ = π ^ 2 := by
    have h1 : ρ * σ = σ * ρ := hσcomm ⟨ρ, hρQ⟩
    have h2 : ρ * t * ρ⁻¹ = t * σ * t := by
      have h := hσρrel
      rw [htinv] at h
      exact h.symm
    calc ρ * π * ρ⁻¹ = (ρ * σ) * t * ρ⁻¹ := by rw [hπdef]; group
      _ = (σ * ρ) * t * ρ⁻¹ := by rw [h1]
      _ = σ * (ρ * t * ρ⁻¹) := by group
      _ = σ * (t * σ * t) := by rw [h2]
      _ = π ^ 2 := by rw [hπdef]; simp only [pow_two, mul_assoc]
  -- `π ^ 15 = 1`
  have hgen : ∀ n : ℕ, π ^ (2 ^ n) = ρ ^ n * π * (ρ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc π ^ (2 ^ (n + 1)) = (π ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
        _ = (ρ ^ n * π * (ρ ^ n)⁻¹) ^ 2 := by rw [ih]
        _ = ρ ^ n * π ^ 2 * (ρ ^ n)⁻¹ := conj_pow' (ρ ^ n) π 2
        _ = ρ ^ n * (ρ * π * ρ⁻¹) * (ρ ^ n)⁻¹ := by rw [← hconjρ]
        _ = ρ ^ (n + 1) * π * (ρ ^ (n + 1))⁻¹ := by
              rw [pow_succ]
              group
  have hπ16 : π ^ 16 = π := by
    have h := hgen 4
    norm_num at h
    rw [h, hρ4]
    group
  have hπ15 : π ^ 15 = 1 := by
    have h16 : π ^ 15 * π = π := by
      rw [← pow_succ, show (15 + 1 : ℕ) = 16 from rfl, hπ16]
    exact mul_right_cancel (b := π) (by rw [h16, one_mul] : π ^ 15 * π = 1 * π)
  have hπne : π ≠ 1 := by
    intro h1
    have hst : σ * t = 1 := by rw [← hπdef]; exact h1
    have ht_eq : t = σ := by
      calc t = σ * (σ * t) := by rw [← mul_assoc, hσ2, one_mul]
        _ = σ * 1 := by rw [hst]
        _ = σ := mul_one σ
    exact hsplit.not_mem (by rw [ht_eq]; exact hsplit.le hσQ)
  have hdvd15 : orderOf π ∣ 15 := orderOf_dvd_iff_pow_eq_one.mpr hπ15
  have h3π : ¬ 3 ∣ orderOf π := fun h => h3 (h.trans (orderOf_dvd_natCard π))
  have hdvd5 : orderOf π ∣ 5 := by
    have hc : Nat.Coprime (orderOf π) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd (p := 3) (n := orderOf π) (by norm_num)).mpr h3π).symm
    have h53 : orderOf π ∣ 5 * 3 := by
      norm_num
      exact hdvd15
    exact hc.dvd_of_dvd_mul_right h53
  have hπord : orderOf π = 5 := by
    rcases (Nat.dvd_prime (p := 5) (m := orderOf π) (by norm_num)).mp hdvd5 with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hπne
    · exact h5
  -- the key: involutions of `Q` normalising `⟨π⟩` are `1` or `σ`
  have key : ∀ y : Q, y * y = 1 → (∃ k : ℕ, k ≤ 4 ∧ (y : G) * π * (y : G)⁻¹ = π ^ k) →
      (y : G) = 1 ∨ (y : G) = σ := by
    intro y hy2 hk
    obtain ⟨k, hk4, hk⟩ := hk
    have hyG2 : (y : G) * (y : G) = 1 := by
      have h' := congrArg (fun z : Q => (z : G)) hy2
      simpa using h'
    have hyinvsq : (y : G)⁻¹ * (y : G)⁻¹ = 1 := by
      rw [← mul_inv_rev, hyG2, inv_one]
    have hysig : (y : G) * σ = σ * (y : G) := hσcomm y
    have hsq : π ^ (k * k) = π := by
      calc π ^ (k * k) = (π ^ k) ^ k := by rw [pow_mul]
        _ = ((y : G) * π * (y : G)⁻¹) ^ k := by rw [← hk]
        _ = (y : G) * π ^ k * (y : G)⁻¹ := conj_pow' (y : G) π k
        _ = (y : G) * ((y : G) * π * (y : G)⁻¹) * (y : G)⁻¹ := by rw [hk]
        _ = π := by
              rw [show (y : G) * ((y : G) * π * (y : G)⁻¹) * (y : G)⁻¹
                    = ((y : G) * (y : G)) * π * ((y : G)⁻¹ * (y : G)⁻¹) by group, hyG2,
                hyinvsq, one_mul, mul_one]
    interval_cases k
    · -- `k = 0`: `y π y⁻¹ = 1` forces `π = 1`
      rw [pow_zero] at hk
      have hπ1 : π = 1 := by
        calc π = (y : G)⁻¹ * ((y : G) * π * (y : G)⁻¹) * (y : G) := by group
          _ = (y : G)⁻¹ * 1 * (y : G) := by rw [hk]
          _ = 1 := by group
      exact absurd hπ1 hπne
    · -- `k = 1`: `y` commutes with `π`, hence with `t`
      rw [pow_one] at hk
      have hyπ : (y : G) * π = π * (y : G) := by
        calc (y : G) * π = ((y : G) * π * (y : G)⁻¹) * (y : G) := by group
          _ = π * (y : G) := by rw [hk]
      have h1 : (y : G) * (σ * t) = (σ * t) * (y : G) := by rw [← hπdef]; exact hyπ
      have h2 : σ * ((y : G) * (σ * t)) = (y : G) * t := by
        calc σ * ((y : G) * (σ * t)) = σ * (((y : G) * σ) * t) := by rw [mul_assoc]
          _ = σ * ((σ * (y : G)) * t) := by rw [hysig]
          _ = (σ * σ) * ((y : G) * t) := by group
          _ = (y : G) * t := by rw [hσ2, one_mul]
      have hyt : (y : G) * t * (y : G)⁻¹ = t := by
        rw [← h2]
        rw [h1]
        rw [show σ * ((σ * t) * (y : G)) * (y : G)⁻¹
              = (σ * σ) * (t * ((y : G) * (y : G)⁻¹)) by group, hσ2, one_mul,
          mul_inv_cancel, mul_one]
      left
      simpa using congrArg (fun z : Q => (z : G)) (centralizer_Q_t_eq_one hsplit y hyt)
    · -- `k = 2`: `π ^ 4 = π` gives `π ^ 3 = 1`, so `5 ∣ 3`
      exfalso
      have h4 : π ^ 4 = π := by simpa using hsq
      have h3' : π ^ 3 = 1 := by
        have h : π ^ 3 * π = π := by rw [← pow_succ, show (3 + 1 : ℕ) = 4 from rfl, h4]
        exact mul_right_cancel (b := π) (by rw [h, one_mul] : π ^ 3 * π = 1 * π)
      have hd : orderOf π ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3'
      rw [hπord] at hd
      exact absurd hd (by norm_num)
    · -- `k = 3`: `π ^ 9 = π` gives `π ^ 8 = 1`, so `5 ∣ 8`
      exfalso
      have h9 : π ^ 9 = π := by simpa using hsq
      have h8 : π ^ 8 = 1 := by
        have h : π ^ 8 * π = π := by rw [← pow_succ, show (8 + 1 : ℕ) = 9 from rfl, h9]
        exact mul_right_cancel (b := π) (by rw [h, one_mul] : π ^ 8 * π = 1 * π)
      have hd : orderOf π ∣ 8 := orderOf_dvd_iff_pow_eq_one.mpr h8
      rw [hπord] at hd
      exact absurd hd (by norm_num)
    · -- `k = 4`: `y π y⁻¹ = π⁻¹`, so `y σ` centralises `t` and `y σ = 1`
      right
      have hπinv : (σ * t)⁻¹ = t * σ := by rw [mul_inv_rev, htinv, hσinv]
      have hπ4inv : π ^ 4 = π⁻¹ := by
        have h : π ^ 4 * π = 1 := by
          rw [← pow_succ, show (4 + 1 : ℕ) = 5 from rfl, ← hπord]
          exact pow_orderOf_eq_one π
        exact eq_inv_of_mul_eq_one_left h
      have hks : (y : G) * σ * t * (y : G)⁻¹ = t * σ := by
        have h := hk
        rw [hπ4inv] at h
        rw [hπdef, hπinv] at h
        calc (y : G) * σ * t * (y : G)⁻¹ = (y : G) * (σ * t) * (y : G)⁻¹ := by group
          _ = t * σ := h
      have hyty : (y : G) * t * (y : G)⁻¹ = σ * t * σ := by
        have h2 : σ * ((y : G) * σ * t * (y : G)⁻¹) = (y : G) * t * (y : G)⁻¹ := by
          calc σ * ((y : G) * σ * t * (y : G)⁻¹) = (σ * σ) * ((y : G) * t * (y : G)⁻¹) := by
                rw [hysig]
                group
            _ = (y : G) * t * (y : G)⁻¹ := by rw [hσ2, one_mul]
        rw [← h2, hks]
        group
      have hcoe : ((y * ⟨σ, hσQ⟩ : Q) : G) = (y : G) * σ := rfl
      have hcomm : ((y * ⟨σ, hσQ⟩ : Q) : G) * t * (((y * ⟨σ, hσQ⟩ : Q)) : G)⁻¹ = t := by
        rw [hcoe]
        calc (y : G) * σ * t * ((y : G) * σ)⁻¹
            = (y : G) * σ * t * (σ * (y : G)⁻¹) := by rw [mul_inv_rev, hσinv]
          _ = (y : G) * (σ * t * σ) * (y : G)⁻¹ := by group
          _ = (y : G) * ((y : G) * t * (y : G)⁻¹) * (y : G)⁻¹ := by rw [hyty]
          _ = t := by
                rw [show (y : G) * ((y : G) * t * (y : G)⁻¹) * (y : G)⁻¹
                      = ((y : G) * (y : G)) * t * ((y : G)⁻¹ * (y : G)⁻¹) by group,
                  hyG2, hyinvsq, one_mul, mul_one]
      have hone : y * ⟨σ, hσQ⟩ = 1 := centralizer_Q_t_eq_one hsplit (y * ⟨σ, hσQ⟩) hcomm
      have hyσ : (y : G) * σ = 1 := by
        have h' := congrArg (fun z : Q => (z : G)) hone
        simpa using h'
      rw [← hσinv]
      exact eq_inv_of_mul_eq_one_left hyσ
  -- apply the key lemma to `ρ²`
  have hρ2σ : ρ ^ 2 = σ := by
    have hρ2Q : ρ ^ 2 ∈ Q := Q.pow_mem hρQ 2
    have hy2 : (⟨ρ ^ 2, hρ2Q⟩ : Q) * ⟨ρ ^ 2, hρ2Q⟩ = 1 := by
      apply Subtype.ext
      show ρ ^ 2 * ρ ^ 2 = ((1 : Q) : G)
      rw [← pow_add, show (2 + 2 : ℕ) = 4 from rfl, hρ4]
      rfl
    have hconj2 : ((⟨ρ ^ 2, hρ2Q⟩ : Q) : G) * π * (((⟨ρ ^ 2, hρ2Q⟩ : Q)) : G)⁻¹ = π ^ 4 := by
      show ρ ^ 2 * π * (ρ ^ 2)⁻¹ = π ^ 4
      have hsq : (ρ * ρ) * π * (ρ⁻¹ * ρ⁻¹) = π ^ 4 := by
        calc (ρ * ρ) * π * (ρ⁻¹ * ρ⁻¹) = ρ * (ρ * π * ρ⁻¹) * ρ⁻¹ := by group
          _ = ρ * (π ^ 2) * ρ⁻¹ := by rw [← hconjρ]
          _ = (ρ * π * ρ⁻¹) ^ 2 := (conj_pow' ρ π 2).symm
          _ = (π ^ 2) ^ 2 := by rw [← hconjρ]
          _ = π ^ 4 := by rw [← pow_mul]
      calc ρ ^ 2 * π * (ρ ^ 2)⁻¹ = (ρ * ρ) * π * (ρ⁻¹ * ρ⁻¹) := by rw [pow_two, mul_inv_rev]
        _ = π ^ 4 := hsq
    rcases key ⟨ρ ^ 2, hρ2Q⟩ hy2 ⟨4, le_refl 4, hconj2⟩ with h1 | h4
    · exfalso
      have hρ2one : ρ ^ 2 = 1 := by
        have h' := h1
        simpa using h'
      have hπ4 : π ^ 4 = π := by
        have h := hgen 2
        norm_num at h
        rw [h, hρ2one]
        group
      have h3' : π ^ 3 = 1 := by
        have h : π ^ 3 * π = π := by rw [← pow_succ, show (3 + 1 : ℕ) = 4 from rfl, hπ4]
        exact mul_right_cancel (b := π) (by rw [h, one_mul] : π ^ 3 * π = 1 * π)
      have hd : orderOf π ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3'
      rw [hπord] at hd
      exact absurd hd (by norm_num)
    · exact h4
  -- conclusion with `g = ρ`
  have hg2 : ((⟨ρ, hρQ⟩ : Q) ^ 2) = ⟨σ, hσQ⟩ := Subtype.ext hρ2σ
  refine ⟨⟨ρ, hρQ⟩, ?_, ?_, ?_⟩
  · rw [hg2]
    exact hcentral ⟨σ, hσQ⟩ (by
      have h' := pow_orderOf_eq_one (⟨σ, hσQ⟩ : Q)
      have hord : orderOf (⟨σ, hσQ⟩ : Q) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact hσord
      rw [hord] at h'
      simpa [pow_two] using h')
  · rw [hg2]
    intro h'
    exact hσne (by
      have h'' := congrArg (fun z : Q => (z : G)) h'
      simpa using h'')
  · rw [hg2]
    show t * (((⟨σ, hσQ⟩ : Q)) : G) * t
      = ((⟨ρ, hρQ⟩ : Q) : G) * t * ((((⟨ρ, hρQ⟩ : Q))⁻¹ : Q) : G)
    simp only [Subgroup.coe_inv]
    simpa [htinv] using hσρrel

end Work.ZassenhausSuzuki
