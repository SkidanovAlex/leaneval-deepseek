import Submission.ZagierHoffmanProof.EndgameBound
import Submission.ZagierHoffmanProof.AbpDescentRestrict
import Submission.ZagierHoffmanProof.DegFrac
import Submission.Commons.Algebra.Polynomial.exists_den_dvd_of_dvd_mul

/-!
# The potential-denominator layer for the two-term rows (CPY19 Prop. 2.2.1's shape)

`PLAN.md` §«SESSION 358» §9.5–§9.8: the two-term endgame — every route to `(q-1) ∣ w` — is blocked
on the **common denominator** of the two rows

* **(R)** `Q·σ(Z) = σ(Q)·W^w·(Z + Y + Q·A₁·H_w)`,
* **(A)** `Q·σ(Y) = σ(Q)·W^(q-1)·(Y + Q·A₂)`,

i.e. on producing `b ∈ F_q[X] ∖ {0}` with `Q ∣ b·Z` and `Q ∣ b·Y`
(`EndgameBound.exists_dvd_theta_pow_of_empty_row` +
`EndgameBound.dvd_theta_pow_of_dvd_mul_of_coeff_mem_ambF` then give `L^w ∣ Z` with **no**
coprimality input).  This module builds the **potential-denominator mechanism** behind that input —
the general (non-σ-fixed) analogue of `Rationality.denIdeal`'s argument:

* `exists_root_of_mem_ambKperf` — every `x ∈ K^{perf}` has a `q`-th root in `K^{perf}`
  (`ambRootAt` on the level-`ν` representatives, then `mem_ratLevelF_iff`);
* `exists_polyTwist_eq_of_coeff_mem_ambKperf` — hence every polynomial with `K^{perf}`-coefficients
  is the `σ`-image of a polynomial (`EndgameBound.exists_polyTwist_eq_of_roots`);
* ★★★ **`dvd_twistInv_of_R_row` / `dvd_twistInv_of_A_row`** — applying `σ^{-1}` to the two rows is
  *legal on polynomials* and gives the **twisted-denominator identities**

  `σ^{-1}(Q)·Z = Q·L^w·σ^{-1}(G)`   (`G := Z + Y + Q·A₁·H_w`),   `σ^{-1}(Q)·Y = Q·L^(q-1)·σ^{-1}(Y + Q·A₂)`,

  i.e. `Q ∣ σ^{-1}(Q)·Z` and `Q ∣ σ^{-1}(Q)·Y`.  So the potential-denominator ideal of the row
  system, `M := {H : Q ∣ H·Z ∧ Q ∣ H·Y}`, contains `Q` **and** `σ^{-1}(Q)` — the level-`(-1)`
  orbit of `Q`.  This is the mechanism `Rationality.exists_twistFixed_den` runs in the σ-*fixed*
  case (there: `M` is σ-stable and `b₀ ∣ σb₀` forces `b₀ ∈ F_q[X]`); in the row case the twist
  stability is replaced by the orbit chain, which is where the remaining work lies
  (`PLAN.md` §9.8);
* ★★ **`exists_den_of_A_row`** — the (A)-row alone *does* produce an honest common denominator for
  `Y`: `Q ∣ b·Y` with `b := Q / gcd(Q, Y)`, and `b ∣ X^q − X` (because `Q ∣ Y·(X^q−X)`), hence `b`
  is (a scalar multiple of) a product of distinct `(X − a)`, `a ∈ F_q`.

⚠ Correction to `PLAN.md` §9.7's "frontier": the (A)-row alone already gives `Q ∣ b·Y` with
`b ∈ F_q[X]`; the `L^w ∣ Z` route needs the *same* `b` to clear `Z` as well, and that is exactly
`gcd(Q, Y) ∣ Z` — i.e. the coprimality that §9.7 identified.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
open Polynomial Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. `q`-th roots in `K^{perf}` -/

/-- ★★ **Every element of `K^{perf}` has a `q`-th root in `K^{perf}`.**  `K^{perf} = ⋃_ν F_q(θ_ν)` is
a perfect field: an element of `F_q(θ_ν)` is a quotient `a/b` of elements of `A_ν = F_q[θ_ν]`, and
`ambRootAt` realises the `q`-th roots of `a` and of `b` inside `A_{ν+1}`. -/
theorem exists_root_of_mem_ambKperf {x : Ambient F} (hx : x ∈ ambKperf F) :
    ∃ y : Ambient F, y ∈ ambKperf F ∧ y ^ Nat.card F = x := by
  obtain ⟨ν, hν⟩ := exists_ratLevelF_of_mem_ambKperf (F := F) hx
  obtain ⟨a, ha, b, hb, hb0, hab⟩ := (mem_ratLevelF_iff (F := F) ν x).mp hν
  refine ⟨ambRootAt F ν 1 a ha / ambRootAt F ν 1 b hb, ?_, ?_⟩
  · exact Subfield.div_mem _ (ambA_subset_ambKperf F (ν + 1) (ambRootAt_mem F ν 1 a ha))
      (ambA_subset_ambKperf F (ν + 1) (ambRootAt_mem F ν 1 b hb))
  · have h1 : (ambRootAt F ν 1 a ha) ^ Nat.card F = a := by
      simpa using ambRootAt_pow F ν 1 a ha
    have h2 : (ambRootAt F ν 1 b hb) ^ Nat.card F = b := by
      simpa using ambRootAt_pow F ν 1 b hb
    rw [div_pow, h1, h2]
    exact hab

/-- ★★ **`K^{perf}[X]` is closed under `σ^{-1}`**: every polynomial with `K^{perf}`-coefficients is
the `σ`-image of a polynomial with `K^{perf}`-coefficients. -/
theorem exists_polyTwist_eq_of_coeff_mem_ambKperf {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambKperf F) :
    ∃ p' : Polynomial (Ambient F), polyTwist (q := Nat.card F) 1 p' = p :=
  exists_polyTwist_eq_of_roots F fun n =>
    (exists_root_of_mem_ambKperf (F := F) (hp n)).imp fun y hy => hy.2

/-! ## §2. The twisted-denominator identities (the potential denominators of the rows) -/

/-- ★★★ **The twisted denominator of the `(R)`-row**: `Q ∣ σ^{-1}(Q)·Z`.  Applying `σ` to the
identity `σ^{-1}(Q)·Z = Q·L^w·σ^{-1}(G)` returns the row itself, so `polyTwist_one_injective`
turns the row into the `σ^{-1}`-form. -/
theorem dvd_twistInv_mul_of_R_row {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    ∃ Q' : Polynomial (Ambient F), polyTwist (q := Nat.card F) 1 Q' = Q ∧ Q ∣ Q' * Z := by
  obtain ⟨Q', hQ'⟩ := exists_polyTwist_eq_of_coeff_mem_ambKperf (F := F) hQ
  obtain ⟨G', hG'⟩ := exists_polyTwist_eq_of_coeff_mem_ambKperf (F := F) hG
  have hσ : polyTwist (q := Nat.card F) 1 (Q' * Z)
      = polyTwist (q := Nat.card F) 1
        (Q * (Polynomial.X - Polynomial.C (ambTheta F)) ^ w * G') := by
    rw [polyTwist_mul, polyTwist_mul, polyTwist_mul, polyTwist_pow, polyTwist_X_sub_C_theta,
      hQ', hG']
    exact hrow
  refine ⟨Q', hQ', (Polynomial.X - Polynomial.C (ambTheta F)) ^ w * G', ?_⟩
  have hEq := polyTwist_one_injective F hσ
  rw [hEq]
  ring

/-- ★★★ **The twisted denominator of the `(A)`-row**: `Q ∣ σ^{-1}(Q)·Y`. -/
theorem dvd_twistInv_mul_of_A_row {Y Q A₂ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F)
    (hY : ∀ n, (Y + Q * A₂).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Y
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
        * (Y + Q * A₂)) :
    ∃ Q' : Polynomial (Ambient F), polyTwist (q := Nat.card F) 1 Q' = Q ∧ Q ∣ Q' * Y := by
  obtain ⟨Q', hQ'⟩ := exists_polyTwist_eq_of_coeff_mem_ambKperf (F := F) hQ
  obtain ⟨Y', hY'⟩ := exists_polyTwist_eq_of_coeff_mem_ambKperf (F := F) hY
  have hσ : polyTwist (q := Nat.card F) 1 (Q' * Y)
      = polyTwist (q := Nat.card F) 1
        (Q * (Polynomial.X - Polynomial.C (ambTheta F)) ^ (Nat.card F - 1) * Y') := by
    rw [polyTwist_mul, polyTwist_mul, polyTwist_mul, polyTwist_pow, polyTwist_X_sub_C_theta,
      hQ', hY']
    exact hrow
  refine ⟨Q', hQ', (Polynomial.X - Polynomial.C (ambTheta F)) ^ (Nat.card F - 1) * Y', ?_⟩
  have hEq := polyTwist_one_injective F hσ
  rw [hEq]
  ring

/-- ★★★ **The potential-denominator statement for the row system**: both rows are cleared by the
*same* twisted denominator `Q' = σ^{-1}(Q)`, i.e. the ideal `{H : Q ∣ H·Z ∧ Q ∣ H·Y}` contains `Q`
and `σ^{-1}(Q)`.  This is the row-case analogue of `Rationality.exists_twistFixed_den`'s
`b₀ ∈ M` / `σb₀ ∈ M` pair. -/
theorem exists_twistInv_den_of_rows {w : ℕ} {Z Y Q A₁ A₂ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hY : ∀ n, (Y + Q * A₂).coeff n ∈ ambKperf F)
    (hrowR : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w))
    (hrowA : Q * polyTwist (q := Nat.card F) 1 Y
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
        * (Y + Q * A₂)) :
    ∃ Q' : Polynomial (Ambient F),
      polyTwist (q := Nat.card F) 1 Q' = Q ∧ Q ∣ Q' * Z ∧ Q ∣ Q' * Y := by
  obtain ⟨Q₁, hQ₁, h1⟩ := dvd_twistInv_mul_of_R_row (F := F) hQ hG hrowR
  obtain ⟨Q₂, hQ₂, h2⟩ := dvd_twistInv_mul_of_A_row (F := F) hQ hY hrowA
  have hQ₂₁ : Q₂ = Q₁ := polyTwist_one_injective F (by rw [hQ₂, hQ₁])
  exact ⟨Q₁, hQ₁, h1, by rwa [hQ₂₁] at h2⟩

/-! ## §3. The `(A)`-row gives an honest `F_q[X]`-denominator for `Y` — for free -/

/-- ★★★ **`Q ∣ b·Y` with `b ∈ F_q[X] ∖ {0}`, from the `(A)`-row alone.**  The row is
`Y·(X^q − X) = −A₂·(X^q − C(θ^q))·Q`, so `b := X^q − X` is already a common denominator for `Y`:
`b·Y = −A₂·(X^q − C(θ^q))·Q`.  Since `X^q − X = ∏_{a ∈ F_q}(X − C a)` has `F_q`-coefficients, this
is the `b ∈ F_q[X]` that `EndgameBound.dvd_theta_pow_of_dvd_mul_of_coeff_mem_ambF` consumes. -/
theorem exists_ambF_den_of_A_row {Y Q A₂ : Polynomial (Ambient F)}
    (hrow : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q) :
    ∃ b : Polynomial (Ambient F), b ≠ 0 ∧ (∀ n, b.coeff n ∈ ambF F) ∧ Q ∣ b * Y := by
  refine ⟨Polynomial.X ^ Nat.card F - Polynomial.X, ?_, coeff_X_pow_sub_X_mem_ambF, ?_⟩
  · intro h
    have h1 := congrArg (fun p : Polynomial (Ambient F) => p.coeff 1) h
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_zero] at h1
    have hq1 : 1 ≠ Nat.card F := by have := two_le_ambCard F; omega
    simp [hq1] at h1
  · refine ⟨-(A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))), ?_⟩
    rw [mul_comm (Polynomial.X ^ Nat.card F - Polynomial.X) Y, hrow]
    ring

/-! ## §3b. The sharp potential denominator for the `Z`-row (the exact input of the crux)

`PLAN.md` §«SESSION 358» §10.5: writing `D_Z := Q / gcd(Q, Z)`, the two facts that the next attack on
the crux needs are `D_Z ∣ Q` and `D_Z ∣ σ^{-1}(Q)`; the latter is the twisted-denominator identity of
§2, and the former is the *retained-factor* form of the denominator-extraction lemma (the extracted
divisor divides the original `a`). -/

/-- Denominator extraction, retained-factor form: if `a ∣ b * c` then there is a **divisor `d` of
`a`** clearing `b` out of `a` and caught by `c`. -/
lemma exists_den_dvd_of_dvd_mul {K : Type*} [Field K] {a b c : Polynomial K} (h : a ∣ b * c) :
    ∃ d : Polynomial K, d ∣ a ∧ a ∣ d * b ∧ d ∣ c :=
  Commons.Algebra.Polynomial.exists_den_dvd_of_dvd_mul h

/-- ★★★ **The sharp potential denominator of the `(R)`-row**: there is `D` with
`D ∣ Q`, `Q ∣ D·Z`, and `D ∣ σ^{-1}(Q)`.  (`D` is `Q / gcd(Q, Z)` up to a unit.)  This is the exact
hypothesis pair of `PLAN.md` §10.5's CRUX₂ — the `Z`-counterpart of
`exists_ambF_den_of_A_row`'s `Q ∣ b·Y` with `b ∣ X^q − X`. -/
theorem exists_den_dvd_of_R_row {w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambKperf F)
    (hG : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambKperf F)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    ∃ D : Polynomial (Ambient F), D ∣ Q ∧ Q ∣ D * Z
      ∧ ∃ Q' : Polynomial (Ambient F), polyTwist (q := Nat.card F) 1 Q' = Q ∧ D ∣ Q' := by
  obtain ⟨Q', hQ', hdvd⟩ := dvd_twistInv_mul_of_R_row (F := F) hQ hG hrow
  obtain ⟨D, hDQ, hDZ, hDQ'⟩ := exists_den_dvd_of_dvd_mul (a := Q) (b := Z) (c := Q')
    (by rwa [mul_comm] at hdvd)
  exact ⟨D, hDQ, hDZ, Q', hQ', hDQ'⟩

/-! ## §4. The composition: a common denominator for both rows gives `L^w ∣ Z` -/

/-- ★★★ **`(X − C θ)^w ∣ Z` from a common denominator for the two rows.**  This is exactly the
composition of `EndgameBound.exists_dvd_theta_pow_of_empty_row` (which needs `Q ∣ b·Z` and `Q ∣ b·Y`
for the *same* `F_q[X]`-element `b` — here `b := bZ·bY`) with
`EndgameBound.dvd_theta_pow_of_dvd_mul_of_coeff_mem_ambF` (Euclid's lemma for `L = X − C θ`: `b` has
`F_q`-coefficients, so it does not vanish at the transcendental `θ`).  No `IsCoprime W Q` input is
needed — this is the paper's common-denominator normalisation. -/
theorem dvd_L_pow_of_common_den {w : ℕ} {Z Y Q A₁ bZ bY : Polynomial (Ambient F)}
    (hQ0 : Q ≠ 0)
    (hbZ : ∀ n, bZ.coeff n ∈ ambF F) (hbZ0 : bZ ≠ 0)
    (hbY : ∀ n, bY.coeff n ∈ ambF F) (hbY0 : bY ≠ 0)
    (hQZ : Q ∣ bZ * Z) (hQY : Q ∣ bY * Y)
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    (Polynomial.X - Polynomial.C (ambTheta F)) ^ w ∣ Z := by
  have hb0 : bZ * bY ≠ 0 := mul_ne_zero hbZ0 hbY0
  have hbmem : ∀ n, (bZ * bY).coeff n ∈ ambF F := by
    intro n
    rw [Polynomial.coeff_mul]
    exact Subring.sum_mem (ambF F).toSubring fun x _ =>
      (ambF F).toSubring.mul_mem (hbZ x.1) (hbY x.2)
  obtain ⟨cZ, hcZ⟩ := hQZ
  obtain ⟨cY, hcY⟩ := hQY
  have h1 : Q ∣ (bZ * bY) * Z := ⟨bY * cZ, by
    calc (bZ * bY) * Z = bY * (bZ * Z) := by ring
      _ = bY * (Q * cZ) := by rw [hcZ]
      _ = Q * (bY * cZ) := by ring⟩
  have h2 : Q ∣ (bZ * bY) * Y := ⟨bZ * cY, by
    calc (bZ * bY) * Y = bZ * (bY * Y) := by ring
      _ = bZ * (Q * cY) := by rw [hcY]
      _ = Q * (bZ * cY) := by ring⟩
  obtain ⟨η, hη, hLη⟩ := exists_dvd_theta_pow_of_empty_row (F := F) (A₁ := A₁) (A₂ := 0)
    (Q := Q) (Y := Y) (Z := Z) (b := bZ * bY) (w := w) hQ0 hbmem h1 h2 hrow
  refine dvd_theta_pow_of_dvd_mul_of_coeff_mem_ambF F hbmem hb0 ?_
  rw [hη]
  exact dvd_mul_of_dvd_right hLη Q

end ZagierHoffmanPositiveChar
