import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.germ_value_defs
import Submission.Work.EQ.germ_poly_identity
import Submission.Work.EQ.germ_sigma_identity
import Submission.Work.EQ.rootMultiplicity_comp_C_mul_X
import Submission.Work.EQ.hasVal_congr
import Submission.Work.EQ.hasVal_exists
import Submission.Work.EQ.parity_core
import Submission.Work.EQ.germ_setup
import Submission.Work.EQ.exists_root_run
import Submission.Work.EQ.orbit_injective
import Submission.Work.EQ.P2p_ne_zero

/-!
# `germ_no_other_roots`

Rychlik's semi-projective argument: if the stable germ `h` of the equichordal half map is
the quotient `N/D` of two coprime polynomials near `0`, then `N` has no root besides `0`.

The proof works with the semi-projective `x`-coordinate
`X(u) = a h(ℓu)/(h(ℓu) - h(u)) - a/2 = Λ(u)/P2(u)`, `ℓ = eqLam a`, and with
`σ(u) = X(ℓu) + X(u) = Ψ(u)/Θ(u)`.  The identity (a corollary of `germ_poly_identity`)

  `σ(u)² (1 + R(ℓu)²) = 1`

puts `σ` on the unit circle at the roots of `N`, so that `X` alternates between the two
reflections `x ↦ ±1 - x` along any chain of roots of `N`, contradicting the endpoint values
`X = ∓a/2`.
-/

namespace Work.EQ

open Polynomial Filter

noncomputable section

open scoped Classical

/-! ## Values of rational functions at a point -/

/-- `(X-Cw)^n ∣ P` and `(X-Cw)^m ∣ Q` imply `(X-Cw)^(n+m) ∣ P*Q`. -/
lemma pow_dvd_mul {P Q : Polynomial ℂ} {w : ℂ} {n m : ℕ}
    (hP : (Polynomial.X - Polynomial.C w) ^ n ∣ P)
    (hQ : (Polynomial.X - Polynomial.C w) ^ m ∣ Q) :
    (Polynomial.X - Polynomial.C w) ^ (n + m) ∣ P * Q := by
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hQ
  refine ⟨P' * Q', ?_⟩
  ring

/-- `(X-Cw)^(ord_w P) ∣ P` for `P ≠ 0`. -/
lemma pow_rootMultiplicity_dvd {P : Polynomial ℂ} (hP : P ≠ 0) (w : ℂ) :
    (Polynomial.X - Polynomial.C w) ^ (P.rootMultiplicity w) ∣ P :=
  (Polynomial.le_rootMultiplicity_iff (p := P) (a := w) (n := P.rootMultiplicity w) hP).mp
    le_rfl

/-- `(X-Cw)^n ∣ P` with `n ≥ 1` implies `P w = 0`. -/
lemma eval_eq_zero_of_dvd {P : Polynomial ℂ} {w : ℂ} {n : ℕ} (hn : 0 < n)
    (h : (Polynomial.X - Polynomial.C w) ^ n ∣ P) : P.eval w = 0 := by
  obtain ⟨Q, rfl⟩ := h
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_pow hn.ne']
  ring

/-- Uniqueness of the value of a rational function at a point. -/
theorem hasVal_unique {A C : Polynomial ℂ} {w L M : ℂ} (hC : C ≠ 0)
    (h1 : HasVal A C w L) (h2 : HasVal A C w M) : L = M := by
  by_contra hLM
  unfold HasVal at h1 h2
  have hsub : (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w + 1)
      ∣ (A - Polynomial.C L * C) - (A - Polynomial.C M * C) := dvd_sub h1 h2
  have hfac : (A - Polynomial.C L * C) - (A - Polynomial.C M * C)
      = (Polynomial.C M - Polynomial.C L) * C := by ring
  rw [hfac] at hsub
  have hCL : Polynomial.C M - Polynomial.C L ≠ 0 := by
    intro h0
    exact hLM (Polynomial.C_injective (sub_eq_zero.mp h0)).symm
  have hne : (Polynomial.C M - Polynomial.C L) * C ≠ 0 := mul_ne_zero hCL hC
  have hge : C.rootMultiplicity w + 1
      ≤ ((Polynomial.C M - Polynomial.C L) * C).rootMultiplicity w := by
    rw [Polynomial.le_rootMultiplicity_iff hne]
    exact hsub
  have heq : (Polynomial.C M - Polynomial.C L).rootMultiplicity w = 0 := by
    rw [show Polynomial.C M - Polynomial.C L = Polynomial.C (M - L) by simp]
    exact Polynomial.rootMultiplicity_C _ _
  rw [Polynomial.rootMultiplicity_mul hne, heq, zero_add] at hge
  omega

/-- The value of a polynomial (with denominator `1`). -/
theorem hasVal_one (A : Polynomial ℂ) (w : ℂ) : HasVal A 1 w (A.eval w) := by
  unfold HasVal
  have h1 : ((1 : Polynomial ℂ)).rootMultiplicity w = 0 := by
    rw [show (1 : Polynomial ℂ) = Polynomial.C (1 : ℂ) by simp]
    exact Polynomial.rootMultiplicity_C _ _
  rw [h1, zero_add, pow_one, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
  simp [Polynomial.eval_sub, Polynomial.eval_C]

/-- A rational function with non-vanishing denominator has its "obvious" value. -/
theorem hasVal_eval {A C : Polynomial ℂ} {w : ℂ} (hC : C.eval w ≠ 0) :
    HasVal A C w (A.eval w / C.eval w) := by
  unfold HasVal
  have hrc : C.rootMultiplicity w = 0 :=
    Polynomial.rootMultiplicity_eq_zero (fun h => hC (Polynomial.IsRoot.def.mp h))
  rw [hrc, zero_add, pow_one, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  field_simp
  ring

/-- Additivity of values. -/
theorem hasVal_add {A C B D : Polynomial ℂ} {w L M : ℂ} (hC : C ≠ 0) (hD : D ≠ 0)
    (hAC : HasVal A C w L) (hBD : HasVal B D w M) :
    HasVal (A * D + B * C) (C * D) w (L + M) := by
  unfold HasVal at *
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hC hD)]
  have key : A * D + B * C - Polynomial.C (L + M) * (C * D)
      = D * (A - Polynomial.C L * C) + C * (B - Polynomial.C M * D) := by
    simp only [Polynomial.C_add]
    ring
  rw [key]
  have h1 : (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w + D.rootMultiplicity w + 1)
      ∣ D * (A - Polynomial.C L * C) := by
    have h := pow_dvd_mul (pow_rootMultiplicity_dvd hD w) hAC
    rwa [show D.rootMultiplicity w + (C.rootMultiplicity w + 1)
      = C.rootMultiplicity w + D.rootMultiplicity w + 1 by omega] at h
  have h2 : (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w + D.rootMultiplicity w + 1)
      ∣ C * (B - Polynomial.C M * D) := by
    have h := pow_dvd_mul (pow_rootMultiplicity_dvd hC w) hBD
    rwa [show C.rootMultiplicity w + (D.rootMultiplicity w + 1)
      = C.rootMultiplicity w + D.rootMultiplicity w + 1 by omega] at h
  exact dvd_add h1 h2

/-- Multiplicativity of values. -/
theorem hasVal_mul {A C B D : Polynomial ℂ} {w L M : ℂ} (hC : C ≠ 0) (hD : D ≠ 0)
    (hAC : HasVal A C w L) (hBD : HasVal B D w M) :
    HasVal (A * B) (C * D) w (L * M) := by
  unfold HasVal at *
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hC hD)]
  have hA : (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w) ∣ A := by
    have h := dvd_add ((pow_dvd_pow _ (Nat.le_succ _)).trans hAC)
      (dvd_mul_of_dvd_right (pow_rootMultiplicity_dvd hC w) (Polynomial.C L))
    rwa [show A - Polynomial.C L * C + Polynomial.C L * C = A by ring] at h
  have key : A * B - Polynomial.C (L * M) * (C * D)
      = A * (B - Polynomial.C M * D) + Polynomial.C M * D * (A - Polynomial.C L * C) := by
    simp only [Polynomial.C_mul]
    ring
  rw [key]
  have h1 : (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w + D.rootMultiplicity w + 1)
      ∣ A * (B - Polynomial.C M * D) := by
    have h := pow_dvd_mul hA hBD
    rwa [show C.rootMultiplicity w + (D.rootMultiplicity w + 1)
      = C.rootMultiplicity w + D.rootMultiplicity w + 1 by omega] at h
  have h2 : (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w + D.rootMultiplicity w + 1)
      ∣ Polynomial.C M * D * (A - Polynomial.C L * C) := by
    have hD' : (Polynomial.X - Polynomial.C w) ^ (D.rootMultiplicity w) ∣ Polynomial.C M * D :=
      dvd_mul_of_dvd_right (pow_rootMultiplicity_dvd hD w) _
    have h := pow_dvd_mul hD' hAC
    rwa [show D.rootMultiplicity w + (C.rootMultiplicity w + 1)
      = C.rootMultiplicity w + D.rootMultiplicity w + 1 by omega] at h
  exact dvd_add h1 h2

/-- The value of `A/C` squares to a value of `A^2/C^2`. -/
theorem hasVal_pow_two {A C : Polynomial ℂ} {w L : ℂ} (hC : C ≠ 0)
    (h : HasVal A C w L) : HasVal (A ^ 2) (C ^ 2) w (L ^ 2) := by
  have h2 := hasVal_mul hC hC h h
  simpa only [pow_two] using h2

end


/-! ## Regularity of a rational function at a point -/

/-- `A/C` is regular (has a finite value) at `w`. -/
def RegAt (A C : Polynomial ℂ) (w : ℂ) : Prop :=
  (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w) ∣ A

lemma hasVal_regAt {A C : Polynomial ℂ} {w L : ℂ} (h : HasVal A C w L) : RegAt A C w := by
  rcases eq_or_ne C 0 with hC | hC
  · subst hC; unfold RegAt; simp
  · unfold HasVal RegAt at *
    have key := dvd_add ((pow_dvd_pow _ (Nat.le_succ _)).trans h)
      (dvd_mul_of_dvd_right (pow_rootMultiplicity_dvd hC w) (Polynomial.C L))
    rwa [show A - Polynomial.C L * C + Polynomial.C L * C = A by ring] at key

lemma regAt_iff {A C : Polynomial ℂ} {w : ℂ} (hC : C ≠ 0) :
    RegAt A C w ↔ ∃ L, HasVal A C w L :=
  ⟨fun h => hasVal_exists hC h, fun ⟨_, h⟩ => hasVal_regAt h⟩

/-- The composition `u ↦ ℓ*u` is injective on polynomials (`ℓ ≠ 0`). -/
lemma comp_C_mul_X_ne_zero {P : Polynomial ℂ} {ℓ : ℂ} (hℓ : ℓ ≠ 0) (hP : P ≠ 0) :
    P.comp (Polynomial.C ℓ * Polynomial.X) ≠ 0 := by
  intro h0
  refine hP (Polynomial.eq_zero_of_infinite_isRoot P ?_)
  suffices h8 : {x : ℂ | P.IsRoot x}.Infinite by exact h8
  have hinj : Function.Injective (fun u : ℂ => ℓ * u) := fun u v huv => mul_left_cancel₀ hℓ huv
  refine (Set.infinite_range_of_injective (f := fun u : ℂ => ℓ * u) hinj).mono ?_
  rintro x ⟨u, rfl⟩
  change P.IsRoot (ℓ * u)
  rw [Polynomial.IsRoot.def]
  have := congrArg (fun Q : Polynomial ℂ => Q.eval u) h0
  simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    mul_div_cancel₀ _ hℓ, Polynomial.eval_zero] using this

/-- Divisibility transfers through `u ↦ ℓ*u`. -/
lemma dvd_comp_C_mul_X {P : Polynomial ℂ} {w ℓ : ℂ} (hℓ : ℓ ≠ 0) {k : ℕ}
    (h : (Polynomial.X - Polynomial.C w) ^ k ∣ P) :
    (Polynomial.X - Polynomial.C (w / ℓ)) ^ k ∣ P.comp (Polynomial.C ℓ * Polynomial.X) := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  refine (Polynomial.le_rootMultiplicity_iff (comp_C_mul_X_ne_zero hℓ hP)).mp ?_
  rw [rootMultiplicity_comp_C_mul_X P w ℓ hℓ]
  exact (Polynomial.le_rootMultiplicity_iff hP).mpr h


/-! ## Generic valuation transfers for `HasVal`

The induction along the chain of roots of `N` needs two transfer lemmas for `HasVal`:
substitution of `u ↦ ℓ*u` in both directions, and cancellation of a common factor. -/

/-- Divisibility transfers back through the substitution `u ↦ ℓ*u`. -/
lemma dvd_of_dvd_comp {P : Polynomial ℂ} {u ℓ : ℂ} (hℓ : ℓ ≠ 0) {k : ℕ}
    (h : (Polynomial.X - Polynomial.C u) ^ k ∣ P.comp (Polynomial.C ℓ * Polynomial.X)) :
    (Polynomial.X - Polynomial.C (ℓ * u)) ^ k ∣ P := by
  rcases eq_or_ne P 0 with hP | hP
  · rw [hP]; exact dvd_zero _
  have hPc : P.comp (Polynomial.C ℓ * Polynomial.X) ≠ 0 := comp_C_mul_X_ne_zero hℓ hP
  have hk : (P.comp (Polynomial.C ℓ * Polynomial.X)).rootMultiplicity u
      = P.rootMultiplicity (ℓ * u) := by
    have h' := rootMultiplicity_comp_C_mul_X P (ℓ * u) ℓ hℓ
    rwa [mul_div_cancel_left₀ u hℓ] at h'
  refine (Polynomial.le_rootMultiplicity_iff hP).mp ?_
  rw [← hk]
  exact (Polynomial.le_rootMultiplicity_iff hPc).mpr h

/-- `HasVal` transfers back through the substitution `u ↦ ℓ*u`. -/
lemma hasVal_of_hasVal_comp {A C : Polynomial ℂ} {u L ℓ : ℂ} (hℓ : ℓ ≠ 0)
    (h : HasVal (A.comp (Polynomial.C ℓ * Polynomial.X))
      (C.comp (Polynomial.C ℓ * Polynomial.X)) u L) :
    HasVal A C (ℓ * u) L := by
  unfold HasVal at h ⊢
  rw [show A.comp (Polynomial.C ℓ * Polynomial.X)
      - Polynomial.C L * C.comp (Polynomial.C ℓ * Polynomial.X)
      = (A - Polynomial.C L * C).comp (Polynomial.C ℓ * Polynomial.X) from by
    rw [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp]] at h
  have hk : (C.comp (Polynomial.C ℓ * Polynomial.X)).rootMultiplicity u
      = C.rootMultiplicity (ℓ * u) := by
    have h' := rootMultiplicity_comp_C_mul_X C (ℓ * u) ℓ hℓ
    rwa [mul_div_cancel_left₀ u hℓ] at h'
  rw [hk] at h
  exact dvd_of_dvd_comp hℓ h

/-- Cancelling a common nonzero factor from a divisibility of powers. -/
lemma dvd_of_dvd_mul {R C : Polynomial ℂ} {u : ℂ} (hC : C ≠ 0) {k : ℕ}
    (h : (Polynomial.X - Polynomial.C u) ^ (C.rootMultiplicity u + k) ∣ R * C) :
    (Polynomial.X - Polynomial.C u) ^ k ∣ R := by
  rcases eq_or_ne R 0 with hR | hR
  · rw [hR]; exact dvd_zero _
  have hRC : R * C ≠ 0 := mul_ne_zero hR hC
  have hle : C.rootMultiplicity u + k ≤ (R * C).rootMultiplicity u :=
    (Polynomial.le_rootMultiplicity_iff hRC).mpr h
  rw [Polynomial.rootMultiplicity_mul hRC] at hle
  exact (Polynomial.le_rootMultiplicity_iff hR).mp (by omega)

/-- **Abstract shift identity.**  If the rational function `Λ/P2` has value `L` at `u`
and `A/Θ = Λ(ℓ·)/P2(ℓ·) + Λ/P2` has value `s` at `u` (with `Θ = P2·P2(ℓ·)` and
`A = Λ(ℓ·)·P2 + Λ·P2(ℓ·)`), then `Λ(ℓ·)/P2(ℓ·) = A/Θ - Λ/P2` has value `s - L` at `u`. -/
lemma hasVal_shift_abstract {Λ Λc P2 P2c A Θ : Polynomial ℂ} {u L s : ℂ}
    (hP2 : P2 ≠ 0) (hP2c : P2c ≠ 0) (hΘ : Θ = P2 * P2c)
    (hA : A = Λc * P2 + Λ * P2c)
    (hL : HasVal Λ P2 u L) (hs : HasVal A Θ u s) :
    HasVal Λc P2c u (s - L) := by
  subst hΘ
  subst hA
  have hord : (P2 * P2c).rootMultiplicity u
      = P2.rootMultiplicity u + P2c.rootMultiplicity u :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hP2 hP2c)
  unfold HasVal at hL hs ⊢
  have hid : (Λc - Polynomial.C (s - L) * P2c) * P2
      = (Λc * P2 + Λ * P2c - Polynomial.C s * (P2 * P2c))
        - (Λ - Polynomial.C L * P2) * P2c := by
    simp only [Polynomial.C_sub]
    ring
  have h1 : (Polynomial.X - Polynomial.C u) ^ ((P2 * P2c).rootMultiplicity u + 1)
      ∣ (Λc * P2 + Λ * P2c - Polynomial.C s * (P2 * P2c)) := hs
  have h2 : (Polynomial.X - Polynomial.C u) ^ ((P2 * P2c).rootMultiplicity u + 1)
      ∣ (Λ - Polynomial.C L * P2) * P2c := by
    have h' := pow_dvd_mul hL (pow_rootMultiplicity_dvd hP2c u)
    rw [show (P2.rootMultiplicity u + 1) + P2c.rootMultiplicity u
        = (P2 * P2c).rootMultiplicity u + 1 by rw [hord]; omega] at h'
    exact h'
  have h3 : (Polynomial.X - Polynomial.C u) ^ ((P2 * P2c).rootMultiplicity u + 1)
      ∣ (Λc - Polynomial.C (s - L) * P2c) * P2 := by
    rw [hid]
    exact dvd_sub h1 h2
  rw [hord] at h3
  exact dvd_of_dvd_mul (k := P2c.rootMultiplicity u + 1) hP2 h3

/-- **The semi-projective shift.**  If `X = Λ/P2` has value `L` at `u` and `σ = Ψ/Θ`
has value `s` at `u`, then `X` has value `s - L` at `ℓ*u`. -/
lemma hasVal_shift {N D : Polynomial ℂ} {a : ℝ} {ℓ u L s : ℂ} (hℓ : ℓ ≠ 0)
    (hP2 : P2p N D ℓ ≠ 0)
    (hL : HasVal (Lam N D (a : ℂ) ℓ) (P2p N D ℓ) u L)
    (hs : HasVal (Psip N D (a : ℂ) ℓ) (ThetaP N D ℓ) u s) :
    HasVal (Lam N D (a : ℂ) ℓ) (P2p N D ℓ) (ℓ * u) (s - L) := by
  have hP2c : (P2p N D ℓ).comp (Polynomial.C ℓ * Polynomial.X) ≠ 0 :=
    comp_C_mul_X_ne_zero hℓ hP2
  refine hasVal_of_hasVal_comp hℓ ?_
  exact hasVal_shift_abstract (Λ := Lam N D (a : ℂ) ℓ)
    (Λc := (Lam N D (a : ℂ) ℓ).comp (Polynomial.C ℓ * Polynomial.X))
    (P2 := P2p N D ℓ) (P2c := (P2p N D ℓ).comp (Polynomial.C ℓ * Polynomial.X))
    (A := Psip N D (a : ℂ) ℓ) (Θ := ThetaP N D ℓ) hP2 hP2c rfl rfl hL hs

/-! ## The value of `σ` at a root of `N(ℓ·)` -/

/-- **`σ = Ψ/Θ` takes the value `±1` at every root of `N(ℓ·)`.**
This is `germ_sigma_value` proved locally (the module `Submission.Work.EQ.germ_sigma_value`
imports the present file, so it cannot be imported here). -/
theorem germ_sigma_value_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {N D : Polynomial ℂ} (hD0 : Polynomial.eval 0 D ≠ 0)
    (hDN : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D = Polynomial.eval u N)
    (hnoCommon : ∀ z : ℂ, Polynomial.eval z N = 0 → Polynomial.eval z D ≠ 0)
    {u : ℂ} (hu : Polynomial.eval ((eqLam a : ℂ) * u) N = 0) :
    ∃ s : ℂ, s ^ 2 = 1 ∧ HasVal (Psip N D (a : ℂ) (eqLam a : ℂ))
      (ThetaP N D (eqLam a : ℂ)) u s := by
  have hid : (Psip N D (a : ℂ) (eqLam a : ℂ)) ^ 2
      * ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X))
      = ((D.comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) ^ 2)
        * (ThetaP N D (eqLam a : ℂ)) ^ 2 := by
    apply Polynomial.funext
    intro v
    have hv := germ_sigma_identity ha0 ha1 hh hD0 hDN v
    simpa [Polynomial.eval_comp] using hv
  have hDℓeval : (D.comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)).eval u ≠ 0 := by
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact hnoCommon _ hu
  have hDℓne : (D.comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) ≠ 0 :=
    fun h0 => hDℓeval (by rw [h0]; simp)
  have hEℓeval : ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)).eval u
      = ((D.comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)).eval u) ^ 2 := by
    rw [show ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)).eval u
        = (N.eval ((eqLam a : ℂ) * u)) ^ 2 + (D.eval ((eqLam a : ℂ) * u)) ^ 2 by
      simp [Ep, Polynomial.eval_comp]]
    rw [hu, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_add]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hEℓne : ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) ≠ 0 := by
    intro h0
    have h1 : ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)).eval u = 0 := by
      rw [h0]; simp
    rw [hEℓeval] at h1
    exact (pow_ne_zero 2 hDℓeval) h1
  by_cases hΘ : ThetaP N D (eqLam a : ℂ) = 0
  · refine ⟨1, one_pow 2, ?_⟩
    have hΨ0 : Psip N D (a : ℂ) (eqLam a : ℂ) = 0 := by
      have h2 : (Psip N D (a : ℂ) (eqLam a : ℂ)) ^ 2
          * ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) = 0 := by
        rw [hid, hΘ]; ring
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h2).resolve_right hEℓne)
    unfold HasVal
    rw [hΘ, hΨ0]
    simp
  · have hΨne : Psip N D (a : ℂ) (eqLam a : ℂ) ≠ 0 := by
      intro h0
      have h2 : (Psip N D (a : ℂ) (eqLam a : ℂ)) ^ 2
          * ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) = 0 := by rw [h0]; ring
      rw [hid] at h2
      exact (mul_ne_zero (pow_ne_zero 2 hDℓne) (pow_ne_zero 2 hΘ)) h2
    have hΘ2 : (ThetaP N D (eqLam a : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hΘ
    have hΨ2 : (Psip N D (a : ℂ) (eqLam a : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hΨne
    have hrm : (Psip N D (a : ℂ) (eqLam a : ℂ)).rootMultiplicity u
        = (ThetaP N D (eqLam a : ℂ)).rootMultiplicity u := by
      have h1 : ((Psip N D (a : ℂ) (eqLam a : ℂ)) ^ 2
            * ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X))).rootMultiplicity u
          = (((D.comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) ^ 2)
            * (ThetaP N D (eqLam a : ℂ)) ^ 2).rootMultiplicity u := by rw [hid]
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hΨ2 hEℓne),
          Polynomial.rootMultiplicity_mul
            (mul_ne_zero (pow_ne_zero 2 hDℓne) hΘ2)] at h1
      have hrmΨ : ((Psip N D (a : ℂ) (eqLam a : ℂ)) ^ 2).rootMultiplicity u
          = 2 * (Psip N D (a : ℂ) (eqLam a : ℂ)).rootMultiplicity u := by
        rw [pow_two, Polynomial.rootMultiplicity_mul (mul_ne_zero hΨne hΨne)]; ring
      have hrmΘ : ((ThetaP N D (eqLam a : ℂ)) ^ 2).rootMultiplicity u
          = 2 * (ThetaP N D (eqLam a : ℂ)).rootMultiplicity u := by
        rw [pow_two, Polynomial.rootMultiplicity_mul (mul_ne_zero hΘ hΘ)]; ring
      have hrmE : ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)).rootMultiplicity u
          = 0 := by
        apply Polynomial.rootMultiplicity_eq_zero
        intro hr
        have h0 : ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)).eval u = 0 :=
          Polynomial.IsRoot.def.mp hr
        rw [hEℓeval] at h0
        exact (pow_ne_zero 2 hDℓeval) h0
      have hrmDℓ2 : (((D.comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) ^ 2)).rootMultiplicity u
          = 0 := by
        apply Polynomial.rootMultiplicity_eq_zero
        intro hr
        have h0 : (((D.comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) ^ 2)).eval u = 0 :=
          Polynomial.IsRoot.def.mp hr
        rw [Polynomial.eval_pow] at h0
        exact (pow_ne_zero 2 hDℓeval) h0
      rw [hrmΨ, hrmE, hrmΘ, hrmDℓ2, add_zero, zero_add] at h1
      omega
    have hReg : RegAt (Psip N D (a : ℂ) (eqLam a : ℂ)) (ThetaP N D (eqLam a : ℂ)) u := by
      unfold RegAt
      exact (Polynomial.le_rootMultiplicity_iff hΨne).mp (le_of_eq hrm.symm)
    obtain ⟨s, hs⟩ := hasVal_exists hΘ hReg
    refine ⟨s, ?_, hs⟩
    have hsq : HasVal ((Psip N D (a : ℂ) (eqLam a : ℂ)) ^ 2)
        ((ThetaP N D (eqLam a : ℂ)) ^ 2) u (s ^ 2) := hasVal_pow_two hΘ hs
    have hone : HasVal ((Psip N D (a : ℂ) (eqLam a : ℂ)) ^ 2)
        ((ThetaP N D (eqLam a : ℂ)) ^ 2) u 1 := by
      have hbase := hasVal_eval (A := ((D.comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) ^ 2))
        (C := ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)))
        (w := u) (by rw [hEℓeval]; exact pow_ne_zero 2 hDℓeval)
      have hval : (((D.comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)) ^ 2).eval u
            / ((Ep N D).comp (Polynomial.C (eqLam a : ℂ) * Polynomial.X)).eval u) = 1 := by
        rw [Polynomial.eval_pow, hEℓeval]
        exact div_self (pow_ne_zero 2 hDℓeval)
      rw [hval] at hbase
      exact hasVal_congr hEℓne hΘ2 hid.symm hbase
    exact hasVal_unique hΘ2 hsq hone

/-! ## Evaluations of the polynomial shapes -/

lemma P2p_eval {N D : Polynomial ℂ} {ℓ : ℂ} (w : ℂ) :
    (P2p N D ℓ).eval w = N.eval (ℓ * w) * D.eval w - N.eval w * D.eval (ℓ * w) := by
  simp only [P2p, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_C, Polynomial.eval_X]

lemma Np_eval {N D : Polynomial ℂ} {ℓ : ℂ} (w : ℂ) :
    (Np N D ℓ).eval w = N.eval w * D.eval (ℓ * w) := by
  simp only [Np, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C,
    Polynomial.eval_X]

lemma Lam_eval {N D : Polynomial ℂ} {a ℓ : ℂ} (w : ℂ) :
    (Lam N D a ℓ).eval w = (a / 2) * (P2p N D ℓ).eval w + a * (Np N D ℓ).eval w := by
  simp only [Lam, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]

/-- The value of `X = Λ/P2` at the low end of a maximal run of roots of `N`. -/
lemma endpoint_value_low' {N D : Polynomial ℂ} {a : ℝ} {ℓ w : ℂ}
    (hD : ∀ z : ℂ, Polynomial.eval z N = 0 → Polynomial.eval z D ≠ 0)
    (hNw : Polynomial.eval w N ≠ 0) (hNlw : Polynomial.eval (ℓ * w) N = 0) :
    (Lam N D (a : ℂ) ℓ).eval w / (P2p N D ℓ).eval w = -(((a / 2 : ℝ)) : ℂ) := by
  rw [Lam_eval, Np_eval, P2p_eval]
  have hDl : D.eval (ℓ * w) ≠ 0 := hD _ hNlw
  rw [hNlw]
  have hne : N.eval w * D.eval (ℓ * w) ≠ 0 := mul_ne_zero hNw hDl
  have hden : 0 * D.eval w - N.eval w * D.eval (ℓ * w) ≠ 0 := by
    rw [zero_mul, zero_sub]; exact neg_ne_zero.mpr hne
  have hnum : (a : ℂ) / 2 * (0 * D.eval w - N.eval w * D.eval (ℓ * w))
        + (a : ℂ) * (N.eval w * D.eval (ℓ * w))
      = -(((a / 2 : ℝ)) : ℂ) * (0 * D.eval w - N.eval w * D.eval (ℓ * w)) := by
    push_cast
    ring
  rw [hnum, mul_div_cancel_right₀ _ hden]

/-- The value of `X = Λ/P2` at the high end of a maximal run of roots of `N`. -/
lemma endpoint_value_high' {N D : Polynomial ℂ} {a : ℝ} {ℓ w : ℂ}
    (hD : ∀ z : ℂ, Polynomial.eval z N = 0 → Polynomial.eval z D ≠ 0)
    (hNw : Polynomial.eval w N = 0) (hNlw : Polynomial.eval (ℓ * w) N ≠ 0) :
    (Lam N D (a : ℂ) ℓ).eval w / (P2p N D ℓ).eval w = (((a / 2 : ℝ)) : ℂ) := by
  rw [Lam_eval, Np_eval, P2p_eval]
  have hDw : D.eval w ≠ 0 := hD _ hNw
  rw [hNw]
  have hne : N.eval (ℓ * w) * D.eval w ≠ 0 := mul_ne_zero hNlw hDw
  have hden : N.eval (ℓ * w) * D.eval w - 0 * D.eval (ℓ * w) ≠ 0 := by
    rw [zero_mul, sub_zero]; exact hne
  have hnum : (a : ℂ) / 2 * (N.eval (ℓ * w) * D.eval w - 0 * D.eval (ℓ * w))
        + (a : ℂ) * (0 * D.eval (ℓ * w))
      = (((a / 2 : ℝ)) : ℂ) * (N.eval (ℓ * w) * D.eval w - 0 * D.eval (ℓ * w)) := by
    push_cast
    ring
  rw [hnum, mul_div_cancel_right₀ _ hden]

/-- Values transfer along `u ↦ ℓ*u`. -/
theorem hasVal_comp_C_mul_X {A C : Polynomial ℂ} {w L : ℂ} {ℓ : ℂ} (hℓ : ℓ ≠ 0)
    (h : HasVal A C w L) :
    HasVal (A.comp (Polynomial.C ℓ * Polynomial.X)) (C.comp (Polynomial.C ℓ * Polynomial.X))
      (w / ℓ) L := by
  unfold HasVal at *
  rw [rootMultiplicity_comp_C_mul_X C w ℓ hℓ]
  have key : A.comp (Polynomial.C ℓ * Polynomial.X)
      - Polynomial.C L * C.comp (Polynomial.C ℓ * Polynomial.X)
      = (A - Polynomial.C L * C).comp (Polynomial.C ℓ * Polynomial.X) := by
    rw [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp]
  rw [key]
  exact dvd_comp_C_mul_X hℓ h

/-- **Propagation.** The roots of `N` are closed under the two neighbours `u/ℓ`, `ℓ*u`
along the orbit of the dynamics. -/
lemma germ_prop {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {N D : Polynomial ℂ} (hD0 : Polynomial.eval 0 D ≠ 0)
    (hDN : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D = Polynomial.eval u N)
    (hnoCommon : ∀ z : ℂ, Polynomial.eval z N = 0 → Polynomial.eval z D ≠ 0)
    (u : ℂ) (hu : Polynomial.eval u N = 0) :
    Polynomial.eval (u / (eqLam a : ℂ)) N = 0 ∨ Polynomial.eval ((eqLam a : ℂ) * u) N = 0 := by
  have key : (Polynomial.eval (u / (eqLam a : ℂ)) N * Polynomial.eval u D) ^ 2
      * (Polynomial.eval ((eqLam a : ℂ) * u) N * Polynomial.eval u D) ^ 2 = 0 := by
    have hh := germ_poly_identity ha0 ha1 hh hD0 hDN u
    rw [hu] at hh
    ring_nf at hh ⊢
    simpa using hh
  have hD : Polynomial.eval u D ≠ 0 := hnoCommon u hu
  rcases mul_eq_zero.mp key with h' | h'
  · left
    exact (mul_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp (by simpa using h'))).resolve_right hD
  · right
    exact (mul_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp (by simpa using h'))).resolve_right hD


/-! ## The main theorem -/

/-- **Rychlik's semi-projective argument (step 1).**  If the stable germ is rational,
`h = N/D` near `0`, with `N` and `D` coprime, then `N` has no root besides `0`. -/
theorem germ_no_other_roots {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {N D : Polynomial ℂ} (hD0 : Polynomial.eval 0 D ≠ 0)
    (hDN : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D = Polynomial.eval u N)
    (hnoCommon : ∀ z : ℂ, Polynomial.eval z N = 0 → Polynomial.eval z D ≠ 0)
    {z : ℂ} (hz : Polynomial.eval z N = 0) : z = 0 := by
  by_contra hz0
  obtain ⟨hN, hN0, hNd⟩ := germ_setup ha0 ha1 hh hD0 hDN
  have hL0 : 0 < eqLam a := by rw [eqLam]; exact div_pos (by linarith) (by linarith)
  have hL1 : eqLam a < 1 := by
    rw [eqLam, div_lt_one (by linarith : (0 : ℝ) < 1 + a)]; linarith
  have hℓ0 : (eqLam a : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hP2ne : P2p N D (eqLam a : ℂ) ≠ 0 := P2p_ne_zero ha0 hN0 hNd hD0
  -- The orbit of `z` under the dilation `u ↦ ℓ*u`.
  set o : ℤ → ℂ := fun n => ((eqLam a ^ n : ℝ) : ℂ) * z with ho
  have ho_zero : o 0 = z := by simp [ho]
  have ho_succ : ∀ n : ℤ, o (n + 1) = (eqLam a : ℂ) * o n := by
    intro n
    simp only [ho]
    rw [zpow_add_one₀ hL0.ne', Complex.ofReal_mul]
    ring
  have ho_inj : Function.Injective o := by
    rw [ho]; exact orbit_injective hL0 hL1 hz0
  -- The set of orbit indices at which `N` vanishes.
  set S : Set ℤ := {n : ℤ | Polynomial.eval (o n) N = 0} with hS
  have hSfin : S.Finite := by
    have hroots : {w : ℂ | N.IsRoot w}.Finite := Polynomial.finite_setOfPred_isRoot hN
    refine (hroots.preimage ho_inj.injOn).subset ?_
    intro n hn
    rw [hS] at hn
    exact Polynomial.IsRoot.def.mpr hn
  have h0S : (0 : ℤ) ∈ S := by
    rw [hS]
    show Polynomial.eval (o 0) N = 0
    rw [ho_zero]; exact hz
  have hprop : ∀ n ∈ S, n - 1 ∈ S ∨ n + 1 ∈ S := by
    intro n hn
    rcases germ_prop ha0 ha1 hh hD0 hDN hnoCommon (o n) hn with h | h
    · left
      have hdiv : o n / (eqLam a : ℂ) = o (n - 1) := by
        have hs := ho_succ (n - 1)
        rw [show n - 1 + 1 = n by ring] at hs
        rw [hs, mul_div_cancel_left₀ _ hℓ0]
      rw [hdiv] at h
      exact h
    · right
      rw [← ho_succ n] at h
      exact h
  obtain ⟨m, M, hm0, h0M, hmM, hrun, hm1, hM1⟩ := exists_root_run S hSfin h0S hprop
  have hSmem : ∀ k : ℤ, m ≤ k → k ≤ M → k ∈ S := fun k h1 h2 =>
    hrun k (by rw [Set.mem_Icc]; exact ⟨h1, h2⟩)
  have hNm : Polynomial.eval (o m) N = 0 := hSmem m le_rfl (by omega)
  have hNM : Polynomial.eval (o M) N = 0 := hSmem M (by omega) le_rfl
  have hDm : Polynomial.eval (o m) D ≠ 0 := hnoCommon _ hNm
  have hDM : Polynomial.eval (o M) D ≠ 0 := hnoCommon _ hNM
  have ho_m : o m = (eqLam a : ℂ) * o (m - 1) := by
    have hs := ho_succ (m - 1)
    rwa [show m - 1 + 1 = m by ring] at hs
  have hNlow : Polynomial.eval (o (m - 1)) N ≠ 0 := fun h0 => hm1 (by rw [hS]; exact h0)
  have hNhigh : Polynomial.eval (o (M + 1)) N ≠ 0 := fun h0 => hM1 (by rw [hS]; exact h0)
  -- The chain `u k = o (m - 1 + k)`, `k = 0, …, K`.
  set K : ℕ := (M - (m - 1)).toNat with hK
  have hKcast : ((K : ℤ)) = M - (m - 1) := by
    rw [hK]; exact Int.toNat_of_nonneg (by omega)
  set u : ℕ → ℂ := fun k => o ((m - 1) + (k : ℤ)) with hu
  have hu_zero : u 0 = o (m - 1) := by simp [hu]
  have hu_K : u K = o M := by
    have h' : (m - 1) + ((K : ℤ)) = M := by rw [hKcast]; ring
    simp only [hu, h']
  have hu_succ : ∀ k : ℕ, u (k + 1) = (eqLam a : ℂ) * u k := by
    intro k
    have h' : (m - 1) + ((k + 1 : ℕ) : ℤ) = ((m - 1) + (k : ℤ)) + 1 := by push_cast; ring
    simp only [hu, h']
    exact ho_succ _
  have hu_mem : ∀ k : ℕ, 1 ≤ k → k ≤ K → (m - 1 + (k : ℤ)) ∈ S := by
    intro k hk1 hk2
    apply hSmem <;> omega
  have hu_shift_mem : ∀ k : ℕ, k < K → (m + (k : ℤ)) ∈ S := by
    intro k hk
    apply hSmem <;> omega
  -- The values of `σ = Ψ/Θ` along the chain.
  have hσex : ∀ k : ℕ, k < K → ∃ s : ℂ, s ^ 2 = 1 ∧
      HasVal (Psip N D (a : ℂ) (eqLam a : ℂ)) (ThetaP N D (eqLam a : ℂ)) (u k) s := by
    intro k hk
    have hhu : Polynomial.eval ((eqLam a : ℂ) * u k) N = 0 := by
      have h1 : (eqLam a : ℂ) * u k = u (k + 1) := (hu_succ k).symm
      have h2 : u (k + 1) = o (m + (k : ℤ)) := by
        have h' : (m - 1) + ((k + 1 : ℕ) : ℤ) = m + (k : ℤ) := by push_cast; ring
        simp only [hu, h']
      rw [h1, h2]
      exact hu_shift_mem k hk
    exact germ_sigma_value_aux (u := u k) ha0 ha1 hh hD0 hDN hnoCommon hhu
  let σv : ℕ → ℂ := fun k => if hk : k < K then (hσex k hk).choose else 0
  have hσspec : ∀ k (hk : k < K), (σv k) ^ 2 = 1 ∧
      HasVal (Psip N D (a : ℂ) (eqLam a : ℂ)) (ThetaP N D (eqLam a : ℂ)) (u k) (σv k) := by
    intro k hk
    simp only [σv]
    rw [dif_pos hk]
    exact (hσex k hk).choose_spec
  -- The denominator does not vanish at the two ends of the chain.
  have hP2_u0 : (P2p N D (eqLam a : ℂ)).eval (u 0) ≠ 0 := by
    rw [hu_zero, P2p_eval, ← ho_m, hNm, zero_mul, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hNlow hDm)
  have hP2_uK : (P2p N D (eqLam a : ℂ)).eval (u K) ≠ 0 := by
    rw [hu_K, P2p_eval, ← ho_succ M, hNM, zero_mul, sub_zero]
    exact mul_ne_zero hNhigh hDM
  have hNl_u0 : Polynomial.eval ((eqLam a : ℂ) * o (m - 1)) N = 0 := by
    rw [← ho_m]; exact hNm
  have hNl_uK : Polynomial.eval ((eqLam a : ℂ) * u K) N ≠ 0 := by
    rw [hu_K, ← ho_succ M]; exact hNhigh
  have hval0 : HasVal (Lam N D (a : ℂ) (eqLam a : ℂ)) (P2p N D (eqLam a : ℂ)) (u 0)
      (-(((a / 2 : ℝ)) : ℂ)) := by
    have h1 := hasVal_eval (A := Lam N D (a : ℂ) (eqLam a : ℂ))
      (C := P2p N D (eqLam a : ℂ)) (w := u 0) hP2_u0
    have h2 : (Lam N D (a : ℂ) (eqLam a : ℂ)).eval (u 0)
        / (P2p N D (eqLam a : ℂ)).eval (u 0) = -(((a / 2 : ℝ)) : ℂ) := by
      rw [hu_zero]
      exact endpoint_value_low' hnoCommon hNlow hNl_u0
    rwa [h2] at h1
  have hvalK : HasVal (Lam N D (a : ℂ) (eqLam a : ℂ)) (P2p N D (eqLam a : ℂ)) (u K)
      (((a / 2 : ℝ)) : ℂ) := by
    have h1 := hasVal_eval (A := Lam N D (a : ℂ) (eqLam a : ℂ))
      (C := P2p N D (eqLam a : ℂ)) (w := u K) hP2_uK
    have h2 : (Lam N D (a : ℂ) (eqLam a : ℂ)).eval (u K)
        / (P2p N D (eqLam a : ℂ)).eval (u K) = (((a / 2 : ℝ)) : ℂ) := by
      rw [hu_K]
      exact endpoint_value_high' hnoCommon hNM (by rw [← ho_succ M]; exact hNhigh)
    rwa [h2] at h1
  -- The chain of values of `X = Λ/P2`.
  let x0 : ℂ := (Lam N D (a : ℂ) (eqLam a : ℂ)).eval (u 0)
    / (P2p N D (eqLam a : ℂ)).eval (u 0)
  let xv : ℕ → ℂ := fun k =>
    Nat.rec x0 (fun j prev => if _ : j < K then σv j - prev else prev) k
  have hxv_zero : xv 0 = x0 := rfl
  have hxv_succ : ∀ k : ℕ, xv (k + 1)
      = if hk : k < K then σv k - xv k else xv k := by
    intro k; rfl
  have hmain : ∀ k : ℕ, k ≤ K → HasVal (Lam N D (a : ℂ) (eqLam a : ℂ))
      (P2p N D (eqLam a : ℂ)) (u k) (xv k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hxv_zero]
      exact hasVal_eval hP2_u0
    | succ k ih =>
      intro hk1
      have hk : k < K := by omega
      have hshift := hasVal_shift (hℓ := hℓ0) (hP2 := hP2ne) (hL := ih (by omega))
        (hs := (hσspec k hk).2)
      rw [← hu_succ k] at hshift
      rw [hxv_succ k, dif_pos hk]
      exact hshift
  have hx0v : xv 0 = -(((a / 2 : ℝ)) : ℂ) :=
    hasVal_unique hP2ne (hmain 0 (by omega)) hval0
  have hxKv : xv K = (((a / 2 : ℝ)) : ℂ) :=
    hasVal_unique hP2ne (hmain K le_rfl) hvalK
  have hrec : ∀ k : ℕ, k < K → ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ xv (k + 1) = ε - xv k := by
    intro k hk
    refine ⟨σv k, ?_, ?_⟩
    · have h2 := (hσspec k hk).1
      have hfac : (σv k - 1) * (σv k + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp hfac with h | h
      · left; linear_combination h
      · right; linear_combination h
    · rw [hxv_succ k, dif_pos hk]
  have hKpos : 1 ≤ K := by
    have h2 : (2 : ℤ) ≤ (K : ℤ) := by rw [hKcast]; omega
    omega
  exact parity_core (a / 2) (by linarith) (by linarith) xv K hKpos hrec hx0v hxKv

end Work.EQ
