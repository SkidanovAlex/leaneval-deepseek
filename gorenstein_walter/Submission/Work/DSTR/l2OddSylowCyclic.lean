/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area DSTR, `Work.DSTR`)

# `Work.DSTR.l2OddSylowCyclic` : Sylow `r`-subgroups of `L₂(q)` for odd `r ≠ p` are cyclic

Let `q = p^k` with `p` an odd prime, `q ≥ 5`, and let `r` be an odd prime, `r ≠ p`.  Then every
Sylow `r`-subgroup of `L₂(q) = PSL(2,GaloisField p k)` is cyclic.

Route.  `|L₂(q)| = q(q²-1)/2`.  For an odd `r ≠ p`, the `r`-part of `|L₂(q)|` is the `r`-part of
`q - 1` when `r ∣ q - 1`, and the `r`-part of `q + 1` when `r ∣ q + 1`; the two cases are
exclusive because `r` is odd.  In the first case the copy of `Fˣ` inside `PSL(2,F)` (the image of
the diagonal torus) is cyclic of order `q - 1`; in the second case the non-split torus
`hypTorus F d = {!![a, d·b; b, a] | a² - d·b² = 1}` (`d` a nonsquare) is cyclic of order `q + 1`.
Either way `L₂(q)` contains a *cyclic* subgroup of order the `r`-part of `|L₂(q)|` — hence a
cyclic Sylow `r`-subgroup — and all Sylow `r`-subgroups are conjugate.
-/
import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.PSL2.Basic
import Submission.Work.PSL2.Card
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff

open scoped MatrixGroups
open Matrix

namespace Work.DSTR

/-! ## 1. Transferring cyclicity from one cyclic subgroup of Sylow order to all Sylow subgroups -/

/-- A cyclic subgroup `H` of order `r ^ v_r(|G|)` is a Sylow `r`-subgroup, so every Sylow
`r`-subgroup of `G` is cyclic (they are all conjugate to `H`). -/
theorem isCyclic_of_sylow_of_cyclic_subgroup {G : Type*} [Group G] [Finite G]
    {r : ℕ} [Fact r.Prime] {H : Subgroup G}
    (hcyc : IsCyclic H) (hcard : Nat.card H = r ^ (Nat.card G).factorization r) :
    ∀ R : Sylow r G, IsCyclic (R : Subgroup G) := by
  intro R
  haveI : Finite (Sylow r G) := Sylow.finite_of_finiteIndex R
  let S : Sylow r G := Sylow.ofCard H hcard
  have hSH : (S : Subgroup G) = H := Sylow.coe_ofCard H hcard
  have hcycS : IsCyclic (S : Subgroup G) := hSH ▸ hcyc
  haveI : IsCyclic (↥S : Type _) := hcycS
  exact (Sylow.equiv S R).isCyclic.mp inferInstance

/-! ## 2. Elements of prime power order in finite cyclic groups -/

/-- In a finite cyclic group, for every prime `r` there is an element of order
`r ^ v_r(|G|)`. -/
theorem exists_orderOf_eq_prime_pow_factorization {G : Type*} [Group G] [Finite G]
    {r : ℕ} (hr : r.Prime) (hcyc : IsCyclic G) :
    ∃ g : G, orderOf g = r ^ (Nat.card G).factorization r := by
  haveI := hcyc
  have h := Nat.Prime.exists_orderOf_eq_pow_factorization_exponent (G := G) hr
  rwa [IsCyclic.exponent_eq_card] at h

/-! ## 3. Elements of odd order survive a quotient by `{1, z}` with `z² = 1` -/

/-- If `f : G →* H` has kernel `{1, z}` with `z ≠ 1` and `z² = 1`, then an element of odd order
has the same order as its image. -/
theorem orderOf_map_eq_of_odd {G H : Type*} [Group G] [Monoid H] (f : G →* H) {z : G}
    (hz2 : z ^ 2 = 1) (hzne : z ≠ 1) (hker : ∀ x : G, f x = 1 ↔ x = 1 ∨ x = z)
    {x : G} (hx : Odd (orderOf x)) : orderOf (f x) = orderOf x := by
  refine Nat.dvd_antisymm (orderOf_map_dvd f x) ?_
  have key : orderOf x ∣ orderOf (f x) := by
    have h1 : f (x ^ orderOf (f x)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
    rcases (hker _).mp h1 with h | h
    · exact orderOf_dvd_of_pow_eq_one h
    · exfalso
      have h2 : x ^ (orderOf (f x) * 2) = 1 := by rw [pow_mul, h, hz2]
      have hd : orderOf x ∣ orderOf (f x) * 2 := orderOf_dvd_of_pow_eq_one h2
      have hdk : orderOf x ∣ orderOf (f x) :=
        Nat.Coprime.dvd_of_dvd_mul_right (Odd.coprime_two_right hx) hd
      have hone : x ^ orderOf (f x) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdk
      rw [hone] at h
      exact hzne h.symm
  exact key

/-! ## 4. The conic `a² - d·b² = 1` over a finite field of odd characteristic, for `d` a
nonsquare, has `q + 1` points -/

/-- For `d ≠ 0` not a square in a finite field of odd characteristic, the conic
`a² - d·b² = 1` has `q + 1` points.  Proof: the slope `(a,b) ↦ b/(1+a)` of the line through
`(-1,0)` is a bijection from the conic minus `(-1,0)` onto all of `F` (the inverse is
`t ↦ ((1 + d t²)/(1 - d t²), 2 t/(1 - d t²))`, and `1 - d t² ≠ 0` for all `t` since `d` is not a
square). -/
theorem ncard_conic_nonsquare (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (d : F) (hd : d ≠ 0) (hnsq : ∀ a : F, a * a ≠ d) :
    {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}.ncard = Nat.card F + 1 := by
  classical
  have hdt : ∀ t : F, d * t ^ 2 ≠ 1 := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0; simp at ht
    · have ht' : d = t⁻¹ * t⁻¹ := by
        calc d = d * (t ^ 2 * (t⁻¹) ^ 2) := by
              rw [← mul_pow, mul_inv_cancel₀ ht0, one_pow, mul_one]
          _ = (d * t ^ 2) * (t⁻¹) ^ 2 := by ring
          _ = (t⁻¹) ^ 2 := by rw [ht, one_mul]
          _ = t⁻¹ * t⁻¹ := by ring
      exact hnsq t⁻¹ ht'.symm
  have hden : ∀ t : F, 1 - d * t ^ 2 ≠ 0 := by
    intro t hh
    exact hdt t (by linear_combination -hh)
  let psi : Option F → F × F := fun m => match m with
    | none => (-1, 0)
    | some t => ((1 + d * t ^ 2) / (1 - d * t ^ 2), 2 * t / (1 - d * t ^ 2))
  let phi : F × F → Option F := fun p => if p = (-1, 0) then none else some (p.2 / (1 + p.1))
  have hpsi_mem : ∀ m : Option F, psi m ∈ {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1} := by
    intro m
    match m with
    | none => simp [psi]
    | some t =>
        simp only [psi, Set.mem_ofPred_eq]
        field_simp [hden t]
        ring
  have h1t : ∀ t : F, 1 + (1 + d * t ^ 2) / (1 - d * t ^ 2) = 2 / (1 - d * t ^ 2) := by
    intro t
    field_simp [hden t]
    ring
  have hphi_psi : ∀ m : Option F, phi (psi m) = m := by
    intro m
    match m with
    | none => simp [phi, psi]
    | some t =>
        have hne : psi (some t) ≠ (-1, 0) := by
          intro hh
          have h1 : 1 + (psi (some t)).1 = 0 := by rw [hh]; norm_num
          rw [show (psi (some t)).1 = (1 + d * t ^ 2) / (1 - d * t ^ 2) from rfl,
            h1t t] at h1
          exact (div_ne_zero h2 (hden t)) h1
        simp only [phi]
        rw [if_neg hne]
        congr 1
        simp only [psi]
        rw [h1t t]
        have hA' : 1 - t ^ 2 * d ≠ 0 := by
          intro h; exact hden t (by linear_combination h)
        field_simp [hA', hden t]
  have hpsi_phi : ∀ p ∈ {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}, psi (phi p) = p := by
    rintro ⟨a, b⟩ hp
    simp only [Set.mem_ofPred_eq] at hp
    by_cases hcase : (a, b) = (-1, 0)
    · rw [hcase]; simp [phi, psi]
    · have h1a : 1 + a ≠ 0 := by
        intro h
        apply hcase
        have ha : a = -1 := by linear_combination h
        have hb2 : d * b ^ 2 = 0 := by rw [ha] at hp; linear_combination -hp
        have hb : b = 0 := by
          rcases mul_eq_zero.mp hb2 with h' | h'
          · exact absurd h' hd
          · have h'' : b * b = 0 := by simpa [pow_two] using h'
            rcases mul_eq_zero.mp h'' with h3 | h3
            · exact h3
            · exact h3
        exact Prod.ext ha hb
      simp only [phi]
      rw [if_neg hcase]
      simp only [psi]
      have hδ : 1 - d * (b / (1 + a)) ^ 2 = 2 / (1 + a) := by
        field_simp [h1a]
        linear_combination hp
      have hν : 1 + d * (b / (1 + a)) ^ 2 = 2 * a / (1 + a) := by
        field_simp [h1a]
        linear_combination -hp
      have hA : (1 + d * (b / (1 + a)) ^ 2) / (1 - d * (b / (1 + a)) ^ 2) = a := by
        rw [hν, hδ]
        field_simp [h1a]
      have hB : 2 * (b / (1 + a)) / (1 - d * (b / (1 + a)) ^ 2) = b := by
        rw [hδ]
        field_simp [h1a]
      exact Prod.ext hA hB
  have key : {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1}.ncard =
      (Set.univ : Set (Option F)).ncard :=
    Set.ncard_congr (fun p _ => phi p) (fun p hp => Set.mem_univ _)
      (fun p q hp hq hpq => by rw [← hpsi_phi p hp, ← hpsi_phi q hq, hpq])
      (fun m _ => ⟨psi m, hpsi_mem m, hphi_psi m⟩)
  rw [key, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_option,
    ← Nat.card_eq_fintype_card]

/-! ## 5. `|hypTorus F d| = q + 1` for a nonsquare `d` -/

/-- The non-split torus `hypTorus F d` of `SL(2,F)` (`F` a finite field of odd characteristic,
`d ≠ 0` a nonsquare) has `q + 1` elements: `(a,b) ↦ !![a, d·b; b, a]` is a bijection onto the
conic `a² - d·b² = 1`. -/
theorem hypTorus_card_nonsquare (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (d : F) (hd : d ≠ 0) (hnsq : ∀ a : F, a * a ≠ d) :
    Nat.card (Work.L2F.hypTorus F d) = Nat.card F + 1 := by
  rw [← ncard_conic_nonsquare F h2 d hd hnsq]
  rw [← Set.ncard_univ (α := ↥(Work.L2F.hypTorus F d))]
  apply Eq.symm
  refine Set.ncard_congr (s := {p : F × F | p.1 ^ 2 - d * p.2 ^ 2 = 1})
    (t := Set.univ) (f := fun p hp =>
      (⟨⟨!![p.1, d * p.2; p.2, p.1], Work.L2F.Conic.hypMat_det d p.1 p.2 hp⟩,
        (Work.L2F.Conic.mem_hypTorus F d _).mpr ⟨p.1, p.2, hp, rfl⟩⟩ : ↥(Work.L2F.hypTorus F d)))
    ?_ ?_ ?_
  · intro p hp; exact Set.mem_univ _
  · intro p q hp hq hpq
    have h1 : p.1 = q.1 := by
      have h := congrArg (fun z : ↥(Work.L2F.hypTorus F d) =>
        (((z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0)) hpq
      simpa using h
    have h2' : p.2 = q.2 := by
      have h := congrArg (fun z : ↥(Work.L2F.hypTorus F d) =>
        (((z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0)) hpq
      simpa using h
    exact Prod.ext h1 h2'
  · intro x _
    obtain ⟨a, b, hab, hx⟩ := (Work.L2F.Conic.mem_hypTorus F d (x : SL(2, F))).mp x.2
    refine ⟨(a, b), hab, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [hx]

/-! ## 6. Arithmetic: the `r`-part of `|L₂(q)|` -/

/-- If `r ≠ 2` is a prime dividing `q - 1` (`q = p^k`, `p` odd, `k ≠ 0`), the `r`-adic valuation
of `|L₂(q)|` equals that of `q - 1`. -/
theorem factorizationCardSplit (p k r : ℕ) [Fact p.Prime] [Fact r.Prime]
    (hk : k ≠ 0) (hp : Odd p) (hr2 : r ≠ 2) (hrp : r ≠ p) (hdvd : r ∣ p ^ k - 1) :
    (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r
      = (p ^ k - 1).factorization r := by
  have hcard := Work.PSL2.card_PSL2_galoisField p k hp hk
  set q := p ^ k with hq
  have hq2 : p ^ (2 * k) = q ^ 2 := by
    rw [hq, ← pow_mul]; congr 1; ring
  rw [hq2] at hcard
  have hG0 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ≠ 0 :=
    Nat.card_pos.ne'
  have hrp' : r.Prime := Fact.out
  have hpp : p.Prime := Fact.out
  have h2f : (2 : ℕ).factorization r = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h with h1 | h1
    · exact hrp'.ne_one h1
    · exact hr2 h1
  have step1 : (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r
      = (2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r := by
    rw [Nat.factorization_mul (by norm_num) hG0, Finsupp.add_apply, h2f, zero_add]
  have hq0 : q ≠ 0 := by rw [hq]; exact pow_ne_zero _ hpp.ne_zero
  have hqge : 2 ≤ q := by
    rw [hq]
    have h1 : (1 : ℕ) ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have h2 : p ≤ p ^ k := by simpa using Nat.pow_le_pow_right hpp.one_le h1
    exact le_trans hpp.two_le h2
  have hq1 : q - 1 ≠ 0 := by omega
  have hq2' : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h := Nat.sq_sub_sq q 1
    simp only [one_pow] at h
    rw [h]; ring
  have step2 : (2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r
      = (q * (q - 1) * (q + 1)).factorization r := by
    rw [hcard, hq2', mul_assoc]
  have hqz : q.factorization r = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro h
    rw [hq] at h
    have hp' : r ∣ p := hrp'.dvd_of_dvd_pow h
    rcases (Nat.dvd_prime hpp).mp hp' with h1 | h1
    · exact hrp'.ne_one h1
    · exact hrp h1
  have hqz1 : (q + 1).factorization r = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro h
    have hd1 : r ∣ q - 1 := by rw [hq]; exact hdvd
    have h2d : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub h hd1
    rw [show (q + 1) - (q - 1) = 2 by omega] at h2d
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h2d with h1 | h1
    · exact hrp'.ne_one h1
    · exact hr2 h1
  have step3 : (q * (q - 1) * (q + 1)).factorization r = (q - 1).factorization r := by
    rw [Nat.factorization_mul (mul_ne_zero hq0 hq1) (by omega : q + 1 ≠ 0),
        Nat.factorization_mul hq0 hq1, Finsupp.add_apply, Finsupp.add_apply, hqz, hqz1,
        add_zero, zero_add]
  calc (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r
      = (2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r := step1
    _ = (q * (q - 1) * (q + 1)).factorization r := step2
    _ = (q - 1).factorization r := step3
    _ = (p ^ k - 1).factorization r := by rw [hq]

/-- If `r ≠ 2` is a prime dividing `q + 1` (`q = p^k`, `p` odd, `k ≠ 0`), the `r`-adic valuation
of `|L₂(q)|` equals that of `q + 1`. -/
theorem factorizationCardNonsplit (p k r : ℕ) [Fact p.Prime] [Fact r.Prime]
    (hk : k ≠ 0) (hp : Odd p) (hr2 : r ≠ 2) (hrp : r ≠ p) (hdvd : r ∣ p ^ k + 1) :
    (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r
      = (p ^ k + 1).factorization r := by
  have hcard := Work.PSL2.card_PSL2_galoisField p k hp hk
  set q := p ^ k with hq
  have hq2 : p ^ (2 * k) = q ^ 2 := by
    rw [hq, ← pow_mul]; congr 1; ring
  rw [hq2] at hcard
  have hG0 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ≠ 0 :=
    Nat.card_pos.ne'
  have hrp' : r.Prime := Fact.out
  have hpp : p.Prime := Fact.out
  have h2f : (2 : ℕ).factorization r = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h with h1 | h1
    · exact hrp'.ne_one h1
    · exact hr2 h1
  have step1 : (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r
      = (2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r := by
    rw [Nat.factorization_mul (by norm_num) hG0, Finsupp.add_apply, h2f, zero_add]
  have hq0 : q ≠ 0 := by rw [hq]; exact pow_ne_zero _ hpp.ne_zero
  have hqge : 2 ≤ q := by
    rw [hq]
    have h1 : (1 : ℕ) ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have h2 : p ≤ p ^ k := by simpa using Nat.pow_le_pow_right hpp.one_le h1
    exact le_trans hpp.two_le h2
  have hq1 : q - 1 ≠ 0 := by omega
  have hq2' : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h := Nat.sq_sub_sq q 1
    simp only [one_pow] at h
    rw [h]; ring
  have step2 : (2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r
      = (q * (q - 1) * (q + 1)).factorization r := by
    rw [hcard, hq2', mul_assoc]
  have hqz : q.factorization r = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro h
    rw [hq] at h
    have hp' : r ∣ p := hrp'.dvd_of_dvd_pow h
    rcases (Nat.dvd_prime hpp).mp hp' with h1 | h1
    · exact hrp'.ne_one h1
    · exact hrp h1
  have hqz1 : (q - 1).factorization r = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro h
    have hd1 : r ∣ q + 1 := by rw [hq]; exact hdvd
    have h2d : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub hd1 h
    rw [show (q + 1) - (q - 1) = 2 by omega] at h2d
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h2d with h1 | h1
    · exact hrp'.ne_one h1
    · exact hr2 h1
  have step3 : (q * (q - 1) * (q + 1)).factorization r = (q + 1).factorization r := by
    rw [Nat.factorization_mul (mul_ne_zero hq0 hq1) (by omega : q + 1 ≠ 0),
        Nat.factorization_mul hq0 hq1, Finsupp.add_apply, Finsupp.add_apply, hqz, hqz1,
        add_zero, zero_add]
  calc (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r
      = (2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).factorization r := step1
    _ = (q * (q - 1) * (q + 1)).factorization r := step2
    _ = (q + 1).factorization r := step3
    _ = (p ^ k + 1).factorization r := by rw [hq]

/-! ## 7. The element `-1` of `SL(2,F)` and the kernel of `pslDiagHom` -/

/-- `(-1)² = 1` in `SL(2,F)`. -/
theorem negOne_sq (F : Type*) [Field F] : Work.L2F.negOne F ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul,
    show ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 from rfl,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- `-1 ≠ 1` in `SL(2,F)` for `F` of odd characteristic. -/
theorem negOne_ne_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Work.L2F.negOne F ≠ 1 := by
  intro h
  have h' : ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by rw [h]
  rw [show ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 from rfl,
    Matrix.SpecialLinearGroup.coe_one] at h'
  have h00 := congrFun (congrFun h' 0) 0
  simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h00
  have hsum : -(1 : F) + 1 = (1 : F) + 1 := by rw [h00]
  rw [neg_add_cancel, one_add_one_eq_two] at hsum
  exact h2 hsum.symm

/-- The kernel of `pslDiagHom : Fˣ →* PSL(2,F)` is `{±1}` for `F` of odd characteristic. -/
theorem pslDiagHom_eq_one_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (a : Fˣ) :
    Work.PSL2.pslDiagHom F a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [show Work.PSL2.pslDiagHom F a = Work.PSL2.pslMap F (Work.PSL2.diag F a) from rfl,
    Work.L2F.Mat2.pslMap_eq_one_iff F h2]
  constructor
  · rintro (h | h)
    · left
      have h' := congrArg (fun z : SL(2, F) => ((z : Matrix (Fin 2) (Fin 2) F)) 0 0) h
      rw [Work.PSL2.coe_diag, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h'
      exact Units.ext h'
    · right
      have h' := congrArg (fun z : SL(2, F) => ((z : Matrix (Fin 2) (Fin 2) F)) 0 0) h
      rw [Work.PSL2.coe_diag] at h'
      simp only [Matrix.of_apply, Matrix.cons_val_zero] at h'
      exact Units.ext (by simpa [Work.L2F.negOne] using h')
  · rintro (h | h)
    · left
      rw [h]
      apply Subtype.ext
      change ((Work.PSL2.diag F (1 : Fˣ) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (1 : Matrix (Fin 2) (Fin 2) F)
      rw [Work.PSL2.coe_diag]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · right
      rw [h]
      apply Subtype.ext
      change ((Work.PSL2.diag F (-1 : Fˣ) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
      rw [Work.PSL2.coe_diag]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Work.L2F.negOne]

/-- For `u : Fˣ` of odd order, `pslDiagHom F u` has the same order as `u`. -/
theorem orderOf_pslDiagHom_of_odd (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) {u : Fˣ}
    (hu : Odd (orderOf u)) :
    orderOf (Work.PSL2.pslDiagHom F u) = orderOf u := by
  have hz2 : (-1 : Fˣ) ^ 2 = 1 := by
    ext
    simp [pow_two]
  have hzne : (-1 : Fˣ) ≠ 1 := by
    intro h
    have h' : (-(1 : F)) = (1 : F) := by
      have h'' : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := congrArg Units.val h
      simpa using h''
    have hsum : -(1 : F) + 1 = (1 : F) + 1 := by rw [h']
    rw [neg_add_cancel, one_add_one_eq_two] at hsum
    exact h2 hsum.symm
  exact orderOf_map_eq_of_odd (Work.PSL2.pslDiagHom F) hz2 hzne
    (pslDiagHom_eq_one_iff F h2) hu

/-! ## 8. A nonsquare in `GaloisField p k` -/

/-- For `p` an odd prime and `k ≠ 0` there is a nonsquare in `GaloisField p k`. -/
theorem exists_nonsquare_galoisField (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : k ≠ 0) :
    ∃ d : GaloisField p k, d ≠ 0 ∧ ∀ a : GaloisField p k, a * a ≠ d := by
  haveI : CharP (GaloisField p k) p := inferInstance
  have hchar : ringChar (GaloisField p k) ≠ 2 := by
    rw [ringChar.eq (GaloisField p k) p]
    intro h
    obtain ⟨m, hm⟩ := hp
    omega
  obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare (F := GaloisField p k) hchar
  refine ⟨d, ?_, ?_⟩
  · intro h0
    exact hd (by rw [h0]; exact ⟨0, by ring⟩)
  · intro a ha
    exact hd ⟨a, ha.symm⟩

/-! ## 9. The main theorem -/

set_option maxHeartbeats 1000000 in
theorem l2OddSylowCyclic : Work.GW2.L2OddSylowCyclicProp := by
  intro p k hpF hp h5 r hrF hr2 hrp R
  let F := GaloisField p k
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := inferInstance
  have htwo : (2 : F) ≠ 0 := by
    intro h
    have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h1 | h1
    · exact hpF.out.ne_one h1
    · obtain ⟨m, hm⟩ := hp
      omega
  have hcardF : Nat.card F = p ^ k := GaloisField.card p k hk
  have hrodd : Odd r := hrF.out.odd_of_ne_two hr2
  by_cases hrG : r ∣ Nat.card (PSL(2, GaloisField p k))
  · -- `r` divides `|L₂(q)|`, hence `r ∣ q² - 1`
    have hdiv : r ∣ p ^ k * (p ^ (2 * k) - 1) := by
      rw [← Work.PSL2.card_PSL2_galoisField p k hp hk]
      exact dvd_mul_of_dvd_right hrG 2
    have hrq : ¬ r ∣ p ^ k := by
      intro h
      have hp' : r ∣ p := hrF.out.dvd_of_dvd_pow h
      rcases (Nat.dvd_prime hpF.out).mp hp' with h1 | h1
      · exact hrF.out.ne_one h1
      · exact hrp h1
    have hdiv2 : r ∣ p ^ (2 * k) - 1 := by
      rcases (hrF.out.dvd_mul).mp hdiv with h | h
      · exact absurd h hrq
      · exact h
    have hfac : p ^ (2 * k) - 1 = (p ^ k - 1) * (p ^ k + 1) := by
      have h : p ^ (2 * k) = (p ^ k) ^ 2 := by rw [← pow_mul]; congr 1; ring
      have h2 := Nat.sq_sub_sq (p ^ k) 1
      simp only [one_pow] at h2
      rw [h, h2]; ring
    rw [hfac] at hdiv2
    rcases (hrF.out.dvd_mul).mp hdiv2 with hcase | hcase
    · -- `r ∣ q - 1`: a cyclic subgroup of order `r^v_r(|G|)` from `Fˣ`
      have harith : (Nat.card Fˣ).factorization r =
          (Nat.card (PSL(2, GaloisField p k))).factorization r := by
        rw [Nat.card_units F, hcardF]
        exact (factorizationCardSplit p k r hk hp hr2 hrp hcase).symm
      obtain ⟨u, hu⟩ := exists_orderOf_eq_prime_pow_factorization (G := Fˣ) hrF.out inferInstance
      rw [harith] at hu
      have hodd : Odd (orderOf u) := by rw [hu]; exact hrodd.pow
      have hx : orderOf (Work.PSL2.pslDiagHom F u) = orderOf u :=
        orderOf_pslDiagHom_of_odd F htwo hodd
      refine isCyclic_of_sylow_of_cyclic_subgroup
        (H := Subgroup.zpowers (Work.PSL2.pslDiagHom F u)) inferInstance ?_ R
      rw [Nat.card_zpowers, hx, hu]
    · -- `r ∣ q + 1`: a cyclic subgroup of order `r^v_r(|G|)` from the non-split torus
      obtain ⟨d, hd0, hnsq⟩ := exists_nonsquare_galoisField p k hp hk
      have hhyp : Nat.card (Work.L2F.hypTorus F d) = p ^ k + 1 := by
        rw [hypTorus_card_nonsquare F htwo d hd0 hnsq, hcardF]
      have harith : (Nat.card (Work.L2F.hypTorus F d)).factorization r =
          (Nat.card (PSL(2, GaloisField p k))).factorization r := by
        rw [hhyp]
        exact (factorizationCardNonsplit p k r hk hp hr2 hrp hcase).symm
      obtain ⟨y, hy⟩ := exists_orderOf_eq_prime_pow_factorization
        (G := ↥(Work.L2F.hypTorus F d)) hrF.out
        (Work.L2F.Conic.hypTorus_cyclic F htwo d hd0)
      rw [harith] at hy
      have hy' : orderOf (y : SL(2, F)) = orderOf y := Subgroup.orderOf_coe y
      have hodd : Odd (orderOf (y : SL(2, F))) := by rw [hy', hy]; exact hrodd.pow
      have hx : orderOf (Work.PSL2.pslMap F (y : SL(2, F))) = orderOf (y : SL(2, F)) :=
        orderOf_map_eq_of_odd (Work.PSL2.pslMap F) (negOne_sq F) (negOne_ne_one F htwo)
          (Work.L2F.Mat2.pslMap_eq_one_iff F htwo) hodd
      refine isCyclic_of_sylow_of_cyclic_subgroup
        (H := Subgroup.zpowers (Work.PSL2.pslMap F (y : SL(2, F)))) inferInstance ?_ R
      rw [Nat.card_zpowers, hx, hy', hy]
  · -- `r ∤ |L₂(q)|`: the trivial subgroup is a cyclic Sylow `r`-subgroup
    refine isCyclic_of_sylow_of_cyclic_subgroup (H := ⊥) inferInstance ?_ R
    rw [Subgroup.card_bot, Nat.factorization_eq_zero_of_not_dvd hrG, pow_zero]

end Work.DSTR
