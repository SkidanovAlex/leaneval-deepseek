import Mathlib
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.MotK.TGen.ZpgI4NInterI

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZpgI4StdIndependent`

The five chart monomials `1, y₁, y₂, y₃, y₁y₃` are linearly independent over `K[y₄]` modulo the
chart ideal `zpgI4 a b h` of the twisted Klein curve, where `y₁ = X 0, y₂ = X 1, y₃ = X 2` and
`y₄ = X 3`.

Two ingredients:

* `Work.MotK.TGen.ZpgI4NInterI` : an element of `zpgI4 a b h` whose monomials avoid the five
  leading monomials `y₂y₃, y₂², y₁y₂, y₁², y₃²` vanishes;
* an insertion argument: inserting `y₄ ↦ T` and suitable `0`/`1` values in the other three
  coordinates isolates the five coefficients one after another.
-/

namespace Work.MotK.TGen

open MvPolynomial

set_option maxHeartbeats 1000000

section Aux

variable {K : Type} [Field K]

/-- The chart variable receiving the one-variable polynomial: `X 0 ↦ X 3`. -/
def zsiSig : Fin 1 → Fin 4 := fun _ => 3

/-- The five chart monomials `1, y₁, y₂, y₃, y₁y₃` as exponent vectors (`yᵢ = X (i-1)`). -/
noncomputable def zsiE : Fin 5 → (Fin 4 →₀ ℕ)
  | 0 => 0
  | 1 => Finsupp.single 0 1
  | 2 => Finsupp.single 1 1
  | 3 => Finsupp.single 2 1
  | 4 => Finsupp.single 0 1 + Finsupp.single 2 1

/-- The five points of `Spec K[y₁,y₂,y₃]` used to separate the five coefficients. -/
noncomputable def zsiV : Fin 5 → Fin 4 → MvPolynomial (Fin 1) K
  | 0 => ![0, 0, 0, MvPolynomial.X 0]
  | 1 => ![1, 0, 0, MvPolynomial.X 0]
  | 2 => ![0, 1, 0, MvPolynomial.X 0]
  | 3 => ![0, 0, 1, MvPolynomial.X 0]
  | 4 => ![1, 0, 1, MvPolynomial.X 0]

/-- An exponent vector is *reduced* if it is divisible by none of the five leading monomials
`y₂y₃, y₂², y₁y₂, y₁², y₃²` of the chart quadrics `zpgQ a b h`. -/
abbrev ZsiGood (c : Fin 4 →₀ ℕ) : Prop :=
  ¬ ((Finsupp.single 0 2 : Fin 4 →₀ ℕ) ≤ c) ∧
  ¬ ((Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 4 →₀ ℕ) ≤ c) ∧
  ¬ ((Finsupp.single 1 2 : Fin 4 →₀ ℕ) ≤ c) ∧
  ¬ ((Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) ≤ c) ∧
  ¬ ((Finsupp.single 2 2 : Fin 4 →₀ ℕ) ≤ c)

lemma zsi_not_le_of_coord {b c : Fin 4 →₀ ℕ} {k : Fin 4} (h : c k < b k) : ¬ (b ≤ c) :=
  fun hle => absurd (Finsupp.le_def.mp hle k) (not_le.mpr h)

lemma ZsiGood_of_three {c : Fin 4 →₀ ℕ} (h0 : c 0 = 0) (h1 : c 1 = 0) (h2 : c 2 = 0) :
    ZsiGood c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine zsi_not_le_of_coord (k := 0) ?_; simp [h0]
  · refine zsi_not_le_of_coord (k := 0) ?_; simp [h0]
  · refine zsi_not_le_of_coord (k := 1) ?_; simp [h1]
  · refine zsi_not_le_of_coord (k := 1) ?_; simp [h1]
  · refine zsi_not_le_of_coord (k := 2) ?_; simp [h2]

lemma ZsiGood_e (j : Fin 5) : ZsiGood (zsiE j) := by
  fin_cases j
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact zsi_not_le_of_coord (k := 0) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 0) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 2) (by simp [zsiE])
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact zsi_not_le_of_coord (k := 0) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 2) (by simp [zsiE])
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact zsi_not_le_of_coord (k := 0) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 0) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 2) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 2) (by simp [zsiE])
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact zsi_not_le_of_coord (k := 0) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 0) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 2) (by simp [zsiE])
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact zsi_not_le_of_coord (k := 0) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 1) (by simp [zsiE])
    · exact zsi_not_le_of_coord (k := 2) (by simp [zsiE])

lemma zsiGood_add_aux {c d b : Fin 4 →₀ ℕ} (hb3 : b 3 = 0) (h0 : d 0 = 0) (h1 : d 1 = 0)
    (h2 : d 2 = 0) (hbc : ¬ (b ≤ c)) : ¬ (b ≤ d + c) := by
  intro hle
  apply hbc
  rw [Finsupp.le_def] at hle ⊢
  intro k
  fin_cases k
  · have := hle 0; rw [Finsupp.add_apply, h0, zero_add] at this; exact this
  · have := hle 1; rw [Finsupp.add_apply, h1, zero_add] at this; exact this
  · have := hle 2; rw [Finsupp.add_apply, h2, zero_add] at this; exact this
  · show b 3 ≤ c 3
    rw [hb3]; exact Nat.zero_le _

lemma zsiGood_add {c d : Fin 4 →₀ ℕ} (h0 : d 0 = 0) (h1 : d 1 = 0) (h2 : d 2 = 0)
    (hc : ZsiGood c) : ZsiGood (d + c) := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := hc
  exact ⟨zsiGood_add_aux (b := Finsupp.single 0 2) (by simp) h0 h1 h2 hA,
    zsiGood_add_aux (b := Finsupp.single 0 1 + Finsupp.single 1 1) (by simp) h0 h1 h2 hB,
    zsiGood_add_aux (b := Finsupp.single 1 2) (by simp) h0 h1 h2 hC,
    zsiGood_add_aux (b := Finsupp.single 1 1 + Finsupp.single 2 1) (by simp) h0 h1 h2 hD,
    zsiGood_add_aux (b := Finsupp.single 2 2) (by simp) h0 h1 h2 hE⟩

lemma ZsiGood_add {p q : MvPolynomial (Fin 4) K}
    (hp : ∀ c ∈ p.support, ZsiGood c) (hq : ∀ c ∈ q.support, ZsiGood c) :
    ∀ c ∈ (p + q).support, ZsiGood c := by
  intro c hc
  rw [MvPolynomial.mem_support_iff] at hc
  rw [MvPolynomial.coeff_add] at hc
  rcases eq_or_ne (p.coeff c) 0 with h | h
  · rw [h, zero_add] at hc
    exact hq c (MvPolynomial.mem_support_iff.mpr hc)
  · exact hp c (MvPolynomial.mem_support_iff.mpr h)

lemma ZsiGood_mul {p q : MvPolynomial (Fin 4) K}
    (hp : ∀ c ∈ p.support, c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0)
    (hq : ∀ c ∈ q.support, ZsiGood c) : ∀ c ∈ (p * q).support, ZsiGood c := by
  intro c hc
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ p.support, ∃ y ∈ q.support, x + y = c := by
    simpa only [Finset.mem_add] using MvPolynomial.support_mul p q hc
  subst hxy
  obtain ⟨hx0, hx1, hx2⟩ := hp x hx
  exact zsiGood_add hx0 hx1 hx2 (hq y hy)

/-- A polynomial in the single chart variable `X 3` has support in exponent vectors vanishing on
`X 0, X 1, X 2`. -/
lemma zsi_rename_three {p : MvPolynomial (Fin 1) K} {x : Fin 4 →₀ ℕ}
    (hx : x ∈ (MvPolynomial.rename zsiSig p).support) : x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
  rw [MvPolynomial.support_rename_of_injective
    (f := zsiSig) (by decide : Function.Injective zsiSig)] at hx
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
  have hsub : (u.mapDomain zsiSig).support ⊆ ({3} : Finset (Fin 4)) := by
    intro k hk
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hk)
    rw [← hv]
    exact Finset.mem_singleton.mpr rfl
  refine ⟨?_, ?_, ?_⟩ <;> by_contra h
  · exact absurd (hsub (Finsupp.mem_support_iff.mpr h)) (by simp)
  · exact absurd (hsub (Finsupp.mem_support_iff.mpr h)) (by simp)
  · exact absurd (hsub (Finsupp.mem_support_iff.mpr h)) (by simp)

lemma ZsiGood_X (m : Fin 4) :
    ∀ c ∈ (MvPolynomial.X m : MvPolynomial (Fin 4) K).support, ZsiGood c := by
  intro c hc
  rw [MvPolynomial.support_X] at hc
  rw [Finset.mem_singleton] at hc
  rw [hc]
  fin_cases m
  · exact ZsiGood_e 1
  · exact ZsiGood_e 2
  · exact ZsiGood_e 3
  · exact ZsiGood_of_three (by simp) (by simp) (by simp)

lemma zsi_supp_X02 :
    (MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 4) K).support ⊆ {zsiE 4} := by
  intro c hc
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ (MvPolynomial.X 0 : MvPolynomial (Fin 4) K).support,
      ∃ y ∈ (MvPolynomial.X 2 : MvPolynomial (Fin 4) K).support, x + y = c := by
    simpa only [Finset.mem_add] using
      MvPolynomial.support_mul (MvPolynomial.X 0) (MvPolynomial.X 2) hc
  rw [MvPolynomial.support_X] at hx hy
  rw [Finset.mem_singleton] at hx hy
  rw [Finset.mem_singleton, ← hxy, hx, hy]
  rfl

end Aux

theorem ZpgI4StdIndependent (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (g : Fin 5 → MvPolynomial (Fin 1) K)
    (hg : (MvPolynomial.rename (fun _ => (3 : Fin 4)) (g 0)
        + MvPolynomial.rename (fun _ => (3 : Fin 4)) (g 1) * (MvPolynomial.X 0 : MvPolynomial (Fin 4) K)
        + MvPolynomial.rename (fun _ => (3 : Fin 4)) (g 2) * MvPolynomial.X 1
        + MvPolynomial.rename (fun _ => (3 : Fin 4)) (g 3) * MvPolynomial.X 2
        + MvPolynomial.rename (fun _ => (3 : Fin 4)) (g 4) * (MvPolynomial.X 0 * MvPolynomial.X 2))
      ∈ Work.MotK.TGen.zpgI4 a b h)
    (i : Fin 5) : g i = 0 := by
  let A : MvPolynomial (Fin 4) K := MvPolynomial.rename zsiSig (g 0)
  let B : MvPolynomial (Fin 4) K := MvPolynomial.rename zsiSig (g 1) * MvPolynomial.X 0
  let C : MvPolynomial (Fin 4) K := MvPolynomial.rename zsiSig (g 2) * MvPolynomial.X 1
  let D : MvPolynomial (Fin 4) K := MvPolynomial.rename zsiSig (g 3) * MvPolynomial.X 2
  let E : MvPolynomial (Fin 4) K := MvPolynomial.rename zsiSig (g 4) * (MvPolynomial.X 0 * MvPolynomial.X 2)
  have hgF : (A + B + C + D + E) ∈ Work.MotK.TGen.zpgI4 a b h := hg
  have hA : ∀ c ∈ A.support, ZsiGood c := by
    intro c hc
    obtain ⟨h0, h1, h2⟩ := zsi_rename_three (K := K) hc
    exact ZsiGood_of_three h0 h1 h2
  have hB : ∀ c ∈ B.support, ZsiGood c :=
    ZsiGood_mul (p := MvPolynomial.rename zsiSig (g 1)) (q := (MvPolynomial.X 0 : MvPolynomial (Fin 4) K))
      (fun c hc => zsi_rename_three (K := K) hc) (ZsiGood_X 0)
  have hC : ∀ c ∈ C.support, ZsiGood c :=
    ZsiGood_mul (p := MvPolynomial.rename zsiSig (g 2)) (q := (MvPolynomial.X 1 : MvPolynomial (Fin 4) K))
      (fun c hc => zsi_rename_three (K := K) hc) (ZsiGood_X 1)
  have hD : ∀ c ∈ D.support, ZsiGood c :=
    ZsiGood_mul (p := MvPolynomial.rename zsiSig (g 3)) (q := (MvPolynomial.X 2 : MvPolynomial (Fin 4) K))
      (fun c hc => zsi_rename_three (K := K) hc) (ZsiGood_X 2)
  have hE : ∀ c ∈ E.support, ZsiGood c :=
    ZsiGood_mul (p := MvPolynomial.rename zsiSig (g 4))
      (q := (MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 4) K))
      (fun c hc => zsi_rename_three (K := K) hc)
      (fun c hc => by
        have h := zsi_supp_X02 (K := K) hc
        rw [Finset.mem_singleton] at h
        rw [h]
        exact ZsiGood_e 4)
  have hred : ∀ c ∈ (A + B + C + D + E).support, ZsiGood c :=
    ZsiGood_add (ZsiGood_add (ZsiGood_add (ZsiGood_add hA hB) hC) hD) hE
  have hF0 : A + B + C + D + E = 0 := ZpgI4NInterI K a b h ha hb hh _ hred hgF
  have hv : ∀ (j : Fin 5) (x : Fin 1),
      zsiV (K := K) j (zsiSig x) = (MvPolynomial.X 0 : MvPolynomial (Fin 1) K) := by
    intro j x
    have hsig : zsiSig x = (3 : Fin 4) := rfl
    rw [hsig]
    fin_cases j <;> simp [zsiV]
  have hV : ∀ (v : Fin 4 → MvPolynomial (Fin 1) K),
      (∀ x : Fin 1, v (zsiSig x) = (MvPolynomial.X 0 : MvPolynomial (Fin 1) K)) →
      ∀ p : MvPolynomial (Fin 1) K, MvPolynomial.aeval v (MvPolynomial.rename zsiSig p) = p := by
    intro v hvp p
    rw [MvPolynomial.rename_eq_aeval, MvPolynomial.comp_aeval_apply]
    simp only [Function.comp_apply, MvPolynomial.aeval_X]
    have hfun : (fun x : Fin 1 => v (zsiSig x))
        = (fun _ : Fin 1 => (MvPolynomial.X 0 : MvPolynomial (Fin 1) K)) := funext hvp
    rw [hfun]
    have hfun2 : (fun _ : Fin 1 => (MvPolynomial.X 0 : MvPolynomial (Fin 1) K))
        = (fun i : Fin 1 => MvPolynomial.X i) :=
      funext fun x => congrArg MvPolynomial.X (Subsingleton.elim (0 : Fin 1) x)
    rw [hfun2]
    exact MvPolynomial.aeval_X_left_apply p
  have hA0 : MvPolynomial.aeval (zsiV (K := K) 0) (A + B + C + D + E) = g 0 := by
    change MvPolynomial.aeval (zsiV (K := K) 0)
      (MvPolynomial.rename zsiSig (g 0) + MvPolynomial.rename zsiSig (g 1) * MvPolynomial.X 0
        + MvPolynomial.rename zsiSig (g 2) * MvPolynomial.X 1
        + MvPolynomial.rename zsiSig (g 3) * MvPolynomial.X 2
        + MvPolynomial.rename zsiSig (g 4) * (MvPolynomial.X 0 * MvPolynomial.X 2)) = g 0
    simp only [map_add, map_mul, hV (zsiV (K := K) 0) (hv 0), MvPolynomial.aeval_X]
    simp [zsiV]
  have hA1 : MvPolynomial.aeval (zsiV (K := K) 1) (A + B + C + D + E) = g 0 + g 1 := by
    change MvPolynomial.aeval (zsiV (K := K) 1)
      (MvPolynomial.rename zsiSig (g 0) + MvPolynomial.rename zsiSig (g 1) * MvPolynomial.X 0
        + MvPolynomial.rename zsiSig (g 2) * MvPolynomial.X 1
        + MvPolynomial.rename zsiSig (g 3) * MvPolynomial.X 2
        + MvPolynomial.rename zsiSig (g 4) * (MvPolynomial.X 0 * MvPolynomial.X 2)) = g 0 + g 1
    simp only [map_add, map_mul, hV (zsiV (K := K) 1) (hv 1), MvPolynomial.aeval_X]
    simp [zsiV]
  have hA2 : MvPolynomial.aeval (zsiV (K := K) 2) (A + B + C + D + E) = g 0 + g 2 := by
    change MvPolynomial.aeval (zsiV (K := K) 2)
      (MvPolynomial.rename zsiSig (g 0) + MvPolynomial.rename zsiSig (g 1) * MvPolynomial.X 0
        + MvPolynomial.rename zsiSig (g 2) * MvPolynomial.X 1
        + MvPolynomial.rename zsiSig (g 3) * MvPolynomial.X 2
        + MvPolynomial.rename zsiSig (g 4) * (MvPolynomial.X 0 * MvPolynomial.X 2)) = g 0 + g 2
    simp only [map_add, map_mul, hV (zsiV (K := K) 2) (hv 2), MvPolynomial.aeval_X]
    simp [zsiV]
  have hA3 : MvPolynomial.aeval (zsiV (K := K) 3) (A + B + C + D + E) = g 0 + g 3 := by
    change MvPolynomial.aeval (zsiV (K := K) 3)
      (MvPolynomial.rename zsiSig (g 0) + MvPolynomial.rename zsiSig (g 1) * MvPolynomial.X 0
        + MvPolynomial.rename zsiSig (g 2) * MvPolynomial.X 1
        + MvPolynomial.rename zsiSig (g 3) * MvPolynomial.X 2
        + MvPolynomial.rename zsiSig (g 4) * (MvPolynomial.X 0 * MvPolynomial.X 2)) = g 0 + g 3
    simp only [map_add, map_mul, hV (zsiV (K := K) 3) (hv 3), MvPolynomial.aeval_X]
    simp [zsiV]
  have hA4 : MvPolynomial.aeval (zsiV (K := K) 4) (A + B + C + D + E) = g 0 + g 1 + g 3 + g 4 := by
    change MvPolynomial.aeval (zsiV (K := K) 4)
      (MvPolynomial.rename zsiSig (g 0) + MvPolynomial.rename zsiSig (g 1) * MvPolynomial.X 0
        + MvPolynomial.rename zsiSig (g 2) * MvPolynomial.X 1
        + MvPolynomial.rename zsiSig (g 3) * MvPolynomial.X 2
        + MvPolynomial.rename zsiSig (g 4) * (MvPolynomial.X 0 * MvPolynomial.X 2)) = g 0 + g 1 + g 3 + g 4
    simp only [map_add, map_mul, hV (zsiV (K := K) 4) (hv 4), MvPolynomial.aeval_X]
    simp [zsiV]
  have h0 : g 0 = 0 := by
    have h := congrArg (MvPolynomial.aeval (zsiV (K := K) 0)) hF0
    simp only [map_zero] at h
    rw [hA0] at h
    exact h
  have h1 : g 1 = 0 := by
    have h := congrArg (MvPolynomial.aeval (zsiV (K := K) 1)) hF0
    simp only [map_zero] at h
    rw [hA1] at h
    rw [h0, zero_add] at h
    exact h
  have h2 : g 2 = 0 := by
    have h := congrArg (MvPolynomial.aeval (zsiV (K := K) 2)) hF0
    simp only [map_zero] at h
    rw [hA2] at h
    rw [h0, zero_add] at h
    exact h
  have h3 : g 3 = 0 := by
    have h := congrArg (MvPolynomial.aeval (zsiV (K := K) 3)) hF0
    simp only [map_zero] at h
    rw [hA3] at h
    rw [h0, zero_add] at h
    exact h
  have h4 : g 4 = 0 := by
    have h := congrArg (MvPolynomial.aeval (zsiV (K := K) 4)) hF0
    simp only [map_zero] at h
    rw [hA4] at h
    rw [h0, h1, h3] at h
    simp only [zero_add] at h
    exact h
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end Work.MotK.TGen
