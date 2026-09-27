import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLComp.tau_algebra

/-!
# Separation at the critical time

Let `τ_p = u₁₀(p₁)u₂₀(p₂)Γ` be the point of `X₃` attached to `(p₁,p₂)`, `a₀ = a(1,1)`, and
`V δ` the entrywise-`δ` neighbourhood of the identity in `SL₃(ℝ)`.  The hypothesis `hinj` is the
uniform injectivity of the `Γ₃`-orbit on the thick set: if all nonzero integral vectors of a
representative `s` have norm `≥ ρ` then no nontrivial conjugate `sγs⁻¹` (`γ ∈ Γ₃`) is `δ`-close
to the identity.

The lemma says that if `τ_p` lies in the Diophantine compact set `Drho ρ` and `n ≥ 1` is a time
at which the two `p`-coordinates are still small (at most `e³ε₀`) but not all small (one is at
least `ε₀`), then `a₀^n τ_p` and `a₀^n τ_{p'}` are not `ε₀`-close.

The mechanism: `a₀ⁿ τ_p = mkX σ` with `σ = a₀ⁿ(u₁₀ p₁ u₂₀ p₂)`, and `σ` is thick because
`a₀ⁿ = a(↑n,↑n)` and `τ_p ∈ Drho ρ`.  If `a₀ⁿ τ_{p'} = g · a₀ⁿ τ_p` with `g ∈ V ε₀`, then
`γ₀ := τ⁻¹(gσ) ∈ Γ₃`, so `σγ₀σ⁻¹ = (u₁₀(-A)u₂₀(-B))·g` with `A = e^{3n}(p'₁-p₁)`,
`B = e^{3n}(p'₂-p₂)`.  Both `u₁₀ u₂₀`-factors and `g` are entrywise within `e³ε₀` and `ε₀` of
the identity, so `σγ₀σ⁻¹ ∈ V δ`; `hinj` forces `γ₀ = 1`, and then `g = u₁₀(A)u₂₀(B)`, whose
off-diagonal entries are `A` and `B`, so `|A|,|B| < ε₀`, contradicting the `hbig` hypothesis.
-/

namespace Work.EKLComp

open Work.EKLContract
open Work.EKLContract.Lemmas

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

noncomputable section

private abbrev u1 (s : ℝ) : SL3 := uij (show (1 : Fin 3) ≠ 0 by decide) s
private abbrev u2 (s : ℝ) : SL3 := uij (show (2 : Fin 3) ≠ 0 by decide) s

private lemma u1_add (a b : ℝ) : u1 (a + b) = u1 a * u1 b :=
  uij_add' (show (1 : Fin 3) ≠ 0 by decide) a b

private lemma u2_add (a b : ℝ) : u2 (a + b) = u2 a * u2 b :=
  uij_add' (show (2 : Fin 3) ≠ 0 by decide) a b

private lemma u1_inv (s : ℝ) : (u1 s)⁻¹ = u1 (-s) :=
  uij_inv' (show (1 : Fin 3) ≠ 0 by decide) s

private lemma u2_inv (s : ℝ) : (u2 s)⁻¹ = u2 (-s) :=
  uij_inv' (show (2 : Fin 3) ≠ 0 by decide) s

private lemma u1u2_comm (s t : ℝ) : u1 s * u2 t = u2 t * u1 s :=
  uij_mul_comm_same_target (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide) s t

/-- `(u₁₀ a u₂₀ b)(u₁₀ c u₂₀ d)⁻¹ = u₁₀(a-c) u₂₀(b-d)`: the inverse-product formula for the
two-parameter unipotent subgroup. -/
private lemma u1u2_mul_inv (a b c d : ℝ) :
    (u1 a * u2 b) * (u1 c * u2 d)⁻¹ = u1 (a - c) * u2 (b - d) := by
  rw [mul_inv_rev, u1_inv, u2_inv]
  rw [← u1u2_comm (-c) (-d)]
  rw [← uij_mul_prod (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide) a b (-c) (-d)]
  rw [show (a : ℝ) + -c = a - c from by ring, show (b : ℝ) + -d = b - d from by ring]

/-- `a(r,s) a(r',s') = a(r+r',s+s')`, i.e. `aPlus` is multiplicative in its parameters. -/
private lemma aPlus_mul_aPlus (r s r' s' : ℝ) :
    aPlus r s * aPlus r' s' = aPlus (r + r') (s + s') := by
  rw [aPlus, aPlus, aPlus, aDiag_add]
  congr 1
  funext k
  fin_cases k <;> simp <;> ring

/-- `a₀ⁿ = a(↑n,↑n)`, the element of the forward semigroup `A⁺` used at the critical time. -/
private lemma a0_pow_eq_aPlus (n : ℕ) : a0 ^ n = aPlus (n : ℝ) (n : ℝ) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, aPlus_zero]
  | succ k ih =>
      rw [pow_succ, ih, a0_eq_aPlus, aPlus_mul_aPlus]
      congr 1 <;> push_cast <;> ring

/-- `(a₀ⁿ P(x,y)) (a₀ⁿ P(x',y'))⁻¹ = u₁₀(e^{3n}(x-x')) u₂₀(e^{3n}(y-y'))` where
`P(x,y) = u₁₀(x)u₂₀(y)`. -/
private lemma sigma_tau_inv (n : ℕ) (x y x' y' : ℝ) :
    (a0 ^ n * (u1 x * u2 y)) * (a0 ^ n * (u1 x' * u2 y'))⁻¹ =
      u1 (Real.exp (3 * (n : ℝ)) * (x - x')) * u2 (Real.exp (3 * (n : ℝ)) * (y - y')) := by
  have hgroup : (a0 ^ n * (u1 x * u2 y)) * (a0 ^ n * (u1 x' * u2 y'))⁻¹
      = a0 ^ n * ((u1 x * u2 y) * (u1 x' * u2 y')⁻¹) * (a0 ^ n)⁻¹ := by group
  rw [hgroup, u1u2_mul_inv]
  exact (tau_algebra).2.1 n (x - x') (y - y')

/-- `1 + 4 e³ < 2600`: the numerical room needed for the `V δ` estimate. -/
private lemma exp3_bound : (1 : ℝ) + 4 * Real.exp 3 < 2600 := by
  have h : Real.exp 3 < 27 := by
    have hpow : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
      ring
    rw [hpow]
    have h0 : (0 : ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
    calc Real.exp 1 ^ 3 < 3 ^ 3 := pow_lt_pow_left₀ Real.exp_one_lt_three h0 (n := 3) (by norm_num)
      _ = 27 := by norm_num
  linarith

/-- Entrywise estimate: if `a, b` are bounded by `E`, `g` is `ε`-close to the identity and
`ε + 4E < δ`, then `(u₁₀ a u₂₀ b)·g` is `δ`-close to the identity.

The entries of `u₁₀(a)u₂₀(b)` are those of the identity except for `(1,0) = a` and `(2,0) = b`,
so multiplying by `g ∈ V ε` perturbs the entries of `g` by at most `|a|·2` and `|b|·2`
(the entries of `g` are bounded by `2`, using `ε ≤ 1`). -/
private lemma V_mul_u1u2 {δ ε E a b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hE0 : 0 ≤ E)
    (hE : ε + 4 * E < δ) {g : SL3} (hg : g ∈ V ε) (ha : |a| ≤ E) (hb : |b| ≤ E) :
    (u1 a * u2 b) * g ∈ V δ := by
  have hP : toMat (u1 a * u2 b) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single (1 : Fin 3) 0 a
        + Matrix.single (2 : Fin 3) 0 b :=
    toMat_uij_mul_same_target (show (1 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) a b
  have hentry : ∀ i j : Fin 3, toMat ((u1 a * u2 b) * g) i j =
      toMat g i j + (if i = 1 then a * toMat g 0 j else 0)
        + (if i = 2 then b * toMat g 0 j else 0) := by
    intro i j
    rw [toMat_mul, hP, Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] <;> ring
  intro i j
  have hgij : |toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε := hg i j
  have hg0j : |toMat g 0 j| ≤ 2 := by
    have h := hg 0 j
    have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j| ≤ 1 := by
      rw [Matrix.one_apply]; split <;> simp
    calc |toMat g 0 j|
        = |(toMat g 0 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j)
            + (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j| := by ring_nf
      _ ≤ |toMat g 0 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j|
            + |(1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j| := abs_add_le _ _
      _ ≤ ε + 1 := add_le_add (le_of_lt h) hone
      _ ≤ 2 := by linarith
  have key : |toMat ((u1 a * u2 b) * g) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ ε + 4 * E := by
    rw [hentry]
    have hX : |(if i = 1 then a * toMat g 0 j else 0)| ≤ |a| * |toMat g 0 j| := by
      split
      · rw [abs_mul]
      · simp only [abs_zero]; positivity
    have hY : |(if i = 2 then b * toMat g 0 j else 0)| ≤ |b| * |toMat g 0 j| := by
      split
      · rw [abs_mul]
      · simp only [abs_zero]; positivity
    have ha' : |a| * |toMat g 0 j| ≤ E * 2 := mul_le_mul ha hg0j (abs_nonneg _) hE0
    have hb' : |b| * |toMat g 0 j| ≤ E * 2 := mul_le_mul hb hg0j (abs_nonneg _) hE0
    have heq : toMat g i j + (if i = 1 then a * toMat g 0 j else 0)
          + (if i = 2 then b * toMat g 0 j else 0)
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
        = (toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
          + (if i = 1 then a * toMat g 0 j else 0)
          + (if i = 2 then b * toMat g 0 j else 0) := by ring
    rw [heq]
    have h1 := abs_add_le ((toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        + (if i = 1 then a * toMat g 0 j else 0)) (if i = 2 then b * toMat g 0 j else 0)
    have h2 := abs_add_le (toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        (if i = 1 then a * toMat g 0 j else 0)
    have hig : |toMat g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ ε := le_of_lt hgij
    linarith [h1, h2, hX, hY, ha', hb', hig, abs_nonneg (toMat g i j),
      abs_nonneg (toMat g 0 j), abs_nonneg (if i = 1 then a * toMat g 0 j else 0),
      abs_nonneg (if i = 2 then b * toMat g 0 j else 0)]
  show |toMat ((u1 a * u2 b) * g) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ
  linarith [key, hE]

end

theorem sep_at_critical_time (ρ δ ε₀ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hε₀ : 0 < ε₀)
    (hε₀1 : ε₀ ≤ 1) (hε₀δ : 2600 * ε₀ ≤ δ)
    (hinj : ∀ s : Work.EKLContract.SL3,
      (∀ m : Fin 3 → ℤ, m ≠ 0 → ρ ≤ ‖Matrix.mulVec (Work.EKLContract.toMat s) (fun j => (m j : ℝ))‖) →
      ∀ γ : Work.EKLContract.SL3, γ ∈ Work.EKLContract.Γ3 → γ ≠ 1 →
        ¬ (s * γ * s⁻¹ ∈ Work.EKLContract.V δ))
    (p p' : ℝ × ℝ) (hp : Work.EKLContract.tau p ∈ Work.EKLContract.Drho ρ)
    (n : ℕ) (hn : 1 ≤ n)
    (hbig : ε₀ ≤ |Real.exp (3 * (n : ℝ)) * (p'.1 - p.1)| ∨ ε₀ ≤ |Real.exp (3 * (n : ℝ)) * (p'.2 - p.2)|)
    (hup : |Real.exp (3 * (n : ℝ)) * (p'.1 - p.1)| ≤ Real.exp 3 * ε₀)
    (hup' : |Real.exp (3 * (n : ℝ)) * (p'.2 - p.2)| ≤ Real.exp 3 * ε₀) :
    ¬ Work.EKLContract.CloseBy ε₀ (Work.EKLContract.a0 ^ n • Work.EKLContract.tau p)
      (Work.EKLContract.a0 ^ n • Work.EKLContract.tau p') := by
  intro hclose
  obtain ⟨g, hgV, hgy⟩ := hclose
  set A : ℝ := Real.exp (3 * (n : ℝ)) * (p'.1 - p.1) with hA
  set B : ℝ := Real.exp (3 * (n : ℝ)) * (p'.2 - p.2) with hB
  set σ : SL3 := a0 ^ n * (u1 p.1 * u2 p.2) with hσ
  set τ : SL3 := a0 ^ n * (u1 p'.1 * u2 p'.2) with hτ
  set γ₀ : SL3 := τ⁻¹ * (g * σ) with hγ₀
  have hAub : |A| ≤ Real.exp 3 * ε₀ := by rw [hA]; exact hup
  have hBub : |B| ≤ Real.exp 3 * ε₀ := by rw [hB]; exact hup'
  have hABbig : ε₀ ≤ |A| ∨ ε₀ ≤ |B| := by rw [hA, hB]; exact hbig
  -- `a₀ⁿ τ_p = mkX σ`, `a₀ⁿ τ_{p'} = mkX τ`
  have hσmk : a0 ^ n • tau p = mkX σ := by
    rw [hσ, show tau p = mkX (u1 p.1 * u2 p.2) from rfl, ← mkX_mul]
  have hτmk : a0 ^ n • tau p' = mkX τ := by
    rw [hτ, show tau p' = mkX (u1 p'.1 * u2 p'.2) from rfl, ← mkX_mul]
  -- the closeness assumption as an element of `Γ₃`
  have hmkτ : mkX τ = mkX (g * σ) := by
    rw [← hτmk, hgy, hσmk, ← mkX_mul]
  have hγ : γ₀ ∈ Γ3 := by
    rw [hγ₀]
    exact QuotientGroup.eq.mp hmkτ
  -- `σ` represents a thick lattice
  have hσthick : mkX σ ∈ Thick ρ := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [← hσmk, a0_pow_eq_aPlus]
    exact hp (n : ℝ) (n : ℝ) hn0 hn0
  -- `σ τ⁻¹ = u₁₀(-A) u₂₀(-B)`
  have hστ : σ * τ⁻¹ = u1 (-A) * u2 (-B) := by
    rw [hσ, hτ, sigma_tau_inv n p.1 p.2 p'.1 p'.2]
    have e1 : Real.exp (3 * (n : ℝ)) * (p.1 - p'.1) = -A := by rw [hA]; ring
    have e2 : Real.exp (3 * (n : ℝ)) * (p.2 - p'.2) = -B := by rw [hB]; ring
    rw [e1, e2]
  have hconj : σ * γ₀ * σ⁻¹ = (u1 (-A) * u2 (-B)) * g := by
    have h1 : σ * γ₀ * σ⁻¹ = σ * τ⁻¹ * g := by rw [hγ₀]; group
    rw [h1, hστ]
  -- the conjugate is `δ`-close to the identity
  have hE0 : 0 ≤ Real.exp 3 * ε₀ := by positivity
  have hEδ : ε₀ + 4 * (Real.exp 3 * ε₀) < δ := by
    have h1 : 4 * Real.exp 3 * ε₀ < 2599 * ε₀ := by
      have : 4 * Real.exp 3 < 2599 := by linarith [exp3_bound]
      exact mul_lt_mul_of_pos_right this hε₀
    nlinarith [h1, hε₀δ]
  have hV : σ * γ₀ * σ⁻¹ ∈ V δ := by
    rw [hconj]
    exact V_mul_u1u2 hε₀ hε₀1 hE0 hEδ hgV (by rw [abs_neg]; exact hAub)
      (by rw [abs_neg]; exact hBub)
  -- the thickness of `σ` in the form of the `hinj` hypothesis
  have hnorm : ∀ m : Fin 3 → ℤ, m ≠ 0 →
      ρ ≤ ‖Matrix.mulVec (toMat σ) (fun j => (m j : ℝ))‖ := by
    intro m hm
    have hno : ¬ HasShortVec (mkX σ) ρ := hσthick
    have hcontra : ¬ (∀ i : Fin 3, |Matrix.mulVec (toMat σ) (fun j => (m j : ℝ)) i| < ρ) := by
      intro hc
      exact hno ⟨σ, rfl, m, hm, fun i => by simpa using hc i⟩
    obtain ⟨i, hi⟩ := not_forall.mp hcontra
    calc ρ ≤ |Matrix.mulVec (toMat σ) (fun j => (m j : ℝ)) i| := not_lt.mp hi
      _ ≤ ‖Matrix.mulVec (toMat σ) (fun j => (m j : ℝ))‖ := by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm _ i
  by_cases hγ1 : γ₀ = 1
  · -- `γ₀ = 1`: then `g = u₁₀(A)u₂₀(B)`, so `|A|,|B| < ε₀`, contradicting `hbig`.
    have hgσ : g * σ = τ := by
      have h2 : τ⁻¹ * (g * σ) = 1 := by rw [← hγ₀]; exact hγ1
      calc g * σ = τ * (τ⁻¹ * (g * σ)) := by group
        _ = τ * 1 := by rw [h2]
        _ = τ := by rw [mul_one]
    have hg_eq : g = τ * σ⁻¹ := by
      calc g = (g * σ) * σ⁻¹ := by group
        _ = τ * σ⁻¹ := by rw [hgσ]
    have hτσ : τ * σ⁻¹ = u1 A * u2 B := by
      rw [hσ, hτ, sigma_tau_inv n p'.1 p'.2 p.1 p.2, ← hA, ← hB]
    have htoMat : toMat (u1 A * u2 B) =
        (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single (1 : Fin 3) 0 A
          + Matrix.single (2 : Fin 3) 0 B :=
      toMat_uij_mul_same_target (show (1 : Fin 3) ≠ 0 by decide)
        (show (2 : Fin 3) ≠ 0 by decide) A B
    have h10 : (u1 A * u2 B) 1 0 = A := by
      show toMat (u1 A * u2 B) 1 0 = A
      rw [htoMat]
      simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h20 : (u1 A * u2 B) 2 0 = B := by
      show toMat (u1 A * u2 B) 2 0 = B
      rw [htoMat]
      simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hone10 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 0 = 0 := by
      rw [Matrix.one_apply, if_neg (show ¬((1 : Fin 3) = 0) by decide)]
    have hone20 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 0 = 0 := by
      rw [Matrix.one_apply, if_neg (show ¬((2 : Fin 3) = 0) by decide)]
    have hAε : |A| < ε₀ := by
      have h := hgV 1 0
      rw [hg_eq, hτσ] at h
      rw [h10, hone10, sub_zero] at h
      exact h
    have hBε : |B| < ε₀ := by
      have h := hgV 2 0
      rw [hg_eq, hτσ] at h
      rw [h20, hone20, sub_zero] at h
      exact h
    rcases hABbig with h | h <;> linarith
  · -- `γ₀ ≠ 1`: `hinj` contradicts `σγ₀σ⁻¹ ∈ V δ`.
    exact (hinj σ hnorm γ₀ hγ hγ1) hV

end Work.EKLComp
