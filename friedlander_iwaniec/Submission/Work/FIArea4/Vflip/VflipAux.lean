import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.pair_sum_le_Evar
import Submission.Work.FIArea4.Evar_le_trivial

/-!
# Auxiliaries for the large-moduli flip (FI §12): the mod-8 splitting and the monoticity of `T12`

Two elementary but load-bearing facts for `Vflip_large` (Friedlander–Iwaniec §12, the range
`R*S < D*D`):

## 1. Splitting the variance into residue classes modulo 8

`Work.FIArea4.Vflip.JacobiFlip.jacobiSym_oddPart_flip` — the pointwise reciprocity flip which is
the arithmetic heart of §12 — needs the pair's moduli `r₁, r₂` to be **congruent modulo 8**
(as in the paper: "by splitting into four residue classes we can assume without loss of generality
that `r` is fixed modulo eight").  For the *pair sum* `Σ_{p,q} α_p ᾱ_q (…)` one cannot simply
restrict to `r₁ ≡ r₂ (mod 8)` by fiat; the correct statement is that the variance is bounded by
`8` times the sum of the variances of the eight truncations `r % 8 = i` of `α`:

`Vvar R S D α ≤ 8 · Σ_{i : Fin 8} Vvar R S D (clsMod8 i α)`.

The proof is the class decomposition `Evar(d) = Σ_a ‖X_a‖²` together with
`α = Σ_i α_i` pointwise and the elementary `‖Σ_i X_i‖² ≤ 8 Σ_i ‖X_i‖²`; **no** Cauchy–Schwarz in
the modulus `d` is involved, so nothing is lost in the `d`-summation.  The `Ener`-weights add up
exactly: `Σ_i p14Ener R S (clsMod8 i α) = p14Ener R S α`.  Consequently the whole §12 estimate may
be proved for arrays supported on a single residue class `r ≡ i (mod 8)`, which is exactly the
hypothesis under which the flip applies — and the reduction `r ↦ r/(r₁,r₂)` (with `(r₁,r₂)` odd,
hence invertible mod 8) *preserves* the class.

## 2. `p14T12` is monotone in `R` and `S`

This is what lets the dyadic decomposition of the pair sum be pushed through: for every dyadic
cell `(R',2R']×(S',2S']` one may use the *full* bracket `p14T12 D R S ε` of the original box.
-/

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Splitting an array into finitely many pieces -/

/-- **Subadditivity of the local variance under a decomposition of the coefficient array.**
If `α r s = Σ_{i : ι} β i r s` pointwise then, by the class decomposition
`Evar(d,α) = Σ_{a<d} ‖Σ_{r̄s≡a} α r s (r|d')‖²`, Cauchy–Schwarz in the (finite) index `ι` gives
`Evar R S d α ≤ #ι · Σ_i Evar R S d (β i)`. -/
lemma Evar_le_card_mul_sum_Evar {ι : Type*} [Fintype ι] (R S d : ℕ) (α : ℕ → ℕ → ℂ)
    (β : ι → ℕ → ℕ → ℂ) (h : ∀ r s, α r s = ∑ i, β i r s) :
    Work.FIPlan.Evar R S d α ≤ (Fintype.card ι : ℝ) * ∑ i, Work.FIPlan.Evar R S d (β i) := by
  have hcls : ∀ a, Work.FIArea4.clsSum R S d α a
      = ∑ i : ι, Work.FIArea4.clsSum R S d (β i) a := by
    intro a
    rw [Work.FIArea4.clsSum]
    calc ∑ p ∈ Work.FIArea4.EvarCls R S d a, α p.1 p.2 * Work.FIArea4.jw d p.1
        = ∑ p ∈ Work.FIArea4.EvarCls R S d a,
            (∑ i : ι, β i p.1 p.2) * Work.FIArea4.jw d p.1 :=
          Finset.sum_congr rfl (fun p _ => by rw [h p.1 p.2])
      _ = ∑ p ∈ Work.FIArea4.EvarCls R S d a,
            ∑ i : ι, β i p.1 p.2 * Work.FIArea4.jw d p.1 :=
          Finset.sum_congr rfl (fun p _ => by rw [Finset.sum_mul])
      _ = ∑ i : ι, ∑ p ∈ Work.FIArea4.EvarCls R S d a,
            β i p.1 p.2 * Work.FIArea4.jw d p.1 := Finset.sum_comm
      _ = ∑ i : ι, Work.FIArea4.clsSum R S d (β i) a :=
          Finset.sum_congr rfl (fun i _ => by rw [Work.FIArea4.clsSum])
  rw [Work.FIArea4.Evar_eq_sum_normSq_clsSum R S d α]
  calc ∑ a ∈ Finset.range d, Complex.normSq (Work.FIArea4.clsSum R S d α a)
      ≤ ∑ a ∈ Finset.range d, (Fintype.card ι : ℝ) *
          ∑ i : ι, Complex.normSq (Work.FIArea4.clsSum R S d (β i) a) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        rw [hcls a]
        exact Work.FIArea4.normSq_sum_le_card_mul_sum Finset.univ _
    _ = (Fintype.card ι : ℝ) *
          ∑ i : ι, ∑ a ∈ Finset.range d,
            Complex.normSq (Work.FIArea4.clsSum R S d (β i) a) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (Fintype.card ι : ℝ) * ∑ i : ι, Work.FIPlan.Evar R S d (β i) := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by rw [Work.FIArea4.Evar_eq_sum_normSq_clsSum])

/-- The same subadditivity for the global variance `V(D) = Σ_{D<d≤2D} E(d)`. -/
lemma Vvar_le_card_mul_sum_Vvar {ι : Type*} [Fintype ι] (R S D : ℕ) (α : ℕ → ℕ → ℂ)
    (β : ι → ℕ → ℕ → ℂ) (h : ∀ r s, α r s = ∑ i, β i r s) :
    Work.FIPlan.Vvar R S D α ≤ (Fintype.card ι : ℝ) * ∑ i, Work.FIPlan.Vvar R S D (β i) := by
  rw [Work.FIPlan.Vvar]
  calc ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d α
      ≤ ∑ d ∈ Finset.Ioc D (2 * D),
          (Fintype.card ι : ℝ) * ∑ i, Work.FIPlan.Evar R S d (β i) :=
        Finset.sum_le_sum (fun d _ => Evar_le_card_mul_sum_Evar R S d α β h)
    _ = (Fintype.card ι : ℝ) *
          ∑ i : ι, ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d (β i) := by
        rw [← Finset.mul_sum, Finset.sum_comm]

/-! ## The eight residue classes modulo `8` -/

/-- `α` truncated to the residue class `r % 8 = i`. -/
def clsMod8 (i : ℕ) (α : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ := fun r s => if r % 8 = i then α r s else 0

lemma clsMod8_of_eq {i r s : ℕ} (α : ℕ → ℕ → ℂ) (h : r % 8 = i) : clsMod8 i α r s = α r s := by
  simp [clsMod8, h]

/-- The support of `clsMod8 i α` lies in the class `r % 8 = i`. -/
lemma clsMod8_support {i r s : ℕ} {α : ℕ → ℕ → ℂ} (h : clsMod8 i α r s ≠ 0) : r % 8 = i := by
  by_contra hc
  exact h (by simp [clsMod8, hc])

/-- Every `r` lies in exactly one class modulo `8`. -/
lemma sum_clsMod8 (α : ℕ → ℕ → ℂ) (r s : ℕ) :
    ∑ i : Fin 8, clsMod8 (i : ℕ) α r s = α r s := by
  rw [Finset.sum_eq_single (⟨r % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)]
  · simp [clsMod8]
  · intro b _ hb
    have h : ¬ (r % 8 = (b : ℕ)) := fun h => hb (Fin.ext h.symm)
    simp only [clsMod8, if_neg h]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The squared norms add up: `Σ_i ‖clsMod8 i α r s‖² = ‖α r s‖²`. -/
lemma sum_normSq_clsMod8 (α : ℕ → ℕ → ℂ) (r s : ℕ) :
    ∑ i : Fin 8, Complex.normSq (clsMod8 (i : ℕ) α r s) = Complex.normSq (α r s) := by
  rw [Finset.sum_eq_single (⟨r % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)]
  · simp [clsMod8]
  · intro b _ hb
    have h : ¬ (r % 8 = (b : ℕ)) := fun h => hb (Fin.ext h.symm)
    simp only [clsMod8, if_neg h, Complex.normSq_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The `τ`-weighted energies of the eight truncations add up to the energy of `α`. -/
lemma sum_p14Ener_clsMod8 (R S : ℕ) (α : ℕ → ℕ → ℂ) :
    ∑ i : Fin 8, Work.FIArea4.p14Ener R S (clsMod8 (i : ℕ) α) = Work.FIArea4.p14Ener R S α := by
  simp only [Work.FIArea4.p14Ener]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.mul_sum, sum_normSq_clsMod8]

/-- **The mod-8 splitting of the variance.**  This is what makes the reciprocity flip of FI §12
available: it reduces the estimate for an arbitrary array `α` to the estimate for the eight
arrays `clsMod8 i α`, each of which is supported on a single class `r ≡ i (mod 8)` — the
hypothesis of `JacobiFlip.jacobiSym_oddPart_flip` (and of `flip_per_pair`).

Since `Σ_i p14Ener R S (clsMod8 i α) = p14Ener R S α`, an estimate of the form
`Vvar R S D β ≤ C·p14T12 D R S ε·p14Ener R S β` for arrays `β` supported on a single class
`r ≡ i (mod 8)` implies the same estimate with constant `8*C` for all `α`. -/
theorem Vvar_mod8 (R S D : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Vvar R S D α
      ≤ 8 * ∑ i : Fin 8, Work.FIPlan.Vvar R S D (clsMod8 (i : ℕ) α) := by
  have h := Vvar_le_card_mul_sum_Vvar R S D α (fun i : Fin 8 => clsMod8 (i : ℕ) α)
    (fun r s => (sum_clsMod8 α r s).symm)
  simpa using h

/-! ## Monotonicity of the bracket `p14T12` -/

/-- **`p14T12 D R S ε` is monotone in `R` and `S`** (for `ε ≥ 0`): every one of its four
summands `D`, `D^{1/3}(RS)^{2/3}(log 2RS+1)^4`, `D^{-1}(RS)^{3/2}(RS)^ε` and
`(RS^{3/4}+SR^{3/4})(RS)^ε` is nondecreasing in `(R,S)` on `R,S ≥ 1`.

This is the tool that lets a dyadic decomposition of the pair sum use the *full* bracket of the
original box `(R,S)` on every cell. -/
lemma p14T12_mono (D : ℕ) {ε : ℝ} (hε : 0 ≤ ε) {R R' S S' : ℕ} (hR : R ≤ R') (hS : S ≤ S')
    (hR1 : 1 ≤ R) (hS1 : 1 ≤ S) :
    Work.FIArea4.p14T12 D R S ε ≤ Work.FIArea4.p14T12 D R' S' ε := by
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg _
  have hR'0 : (0 : ℝ) ≤ (R' : ℝ) := Nat.cast_nonneg _
  have hS'0 : (0 : ℝ) ≤ (S' : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hRR : (R : ℝ) ≤ (R' : ℝ) := by exact_mod_cast hR
  have hSS : (S : ℝ) ≤ (S' : ℝ) := by exact_mod_cast hS
  have hRS : (R : ℝ) * (S : ℝ) ≤ (R' : ℝ) * (S' : ℝ) := mul_le_mul hRR hSS hS0 hR'0
  have hRS0 : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) := mul_nonneg hR0 hS0
  have hRS'0 : (0 : ℝ) ≤ (R' : ℝ) * (S' : ℝ) := mul_nonneg hR'0 hS'0
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hS1' : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS1
  have h2RS : (1 : ℝ) ≤ 2 * (R : ℝ) * (S : ℝ) := by nlinarith
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * (R : ℝ) * (S : ℝ)) := Real.log_nonneg h2RS
  -- the four summands
  have hpow : ((R : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3)
      ≤ ((R' : ℝ) * (S' : ℝ)) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow hRS0 hRS (by norm_num)
  have h32 : ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)
      ≤ ((R' : ℝ) * (S' : ℝ)) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hRS0 hRS (by norm_num)
  have heps : ((R : ℝ) * (S : ℝ)) ^ ε ≤ ((R' : ℝ) * (S' : ℝ)) ^ ε :=
    Real.rpow_le_rpow hRS0 hRS hε
  have hlogmono : Real.log (2 * (R : ℝ) * (S : ℝ)) ≤ Real.log (2 * (R' : ℝ) * (S' : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog4 : (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ (4 : ℕ)
      ≤ (Real.log (2 * (R' : ℝ) * (S' : ℝ)) + 1) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hpL : ((R : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3)
        * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ (4 : ℕ)
      ≤ ((R' : ℝ) * (S' : ℝ)) ^ ((2 : ℝ) / 3)
        * (Real.log (2 * (R' : ℝ) * (S' : ℝ)) + 1) ^ (4 : ℕ) :=
    mul_le_mul hpow hlog4 (by positivity) (by positivity)
  have hmid : (D : ℝ) ^ ((1 : ℝ) / 3) * ((R : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3)
        * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ (4 : ℕ)
      ≤ (D : ℝ) ^ ((1 : ℝ) / 3) * ((R' : ℝ) * (S' : ℝ)) ^ ((2 : ℝ) / 3)
        * (Real.log (2 * (R' : ℝ) * (S' : ℝ)) + 1) ^ (4 : ℕ) := by
    have h1 : (0 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hD0 _
    have := mul_le_mul_of_nonneg_left hpL h1
    simpa only [mul_assoc] using this
  have hA : (D : ℝ)⁻¹ * ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)
      ≤ (D : ℝ)⁻¹ * ((R' : ℝ) * (S' : ℝ)) ^ ((3 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left h32 (by positivity)
  have hB : (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) ≤ (R' : ℝ) * (S' : ℝ) ^ ((3 : ℝ) / 4) := by
    have h : (S : ℝ) ^ ((3 : ℝ) / 4) ≤ (S' : ℝ) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hS0 hSS (by norm_num)
    exact mul_le_mul hRR h (by positivity) hR'0
  have hC : (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) ≤ (S' : ℝ) * (R' : ℝ) ^ ((3 : ℝ) / 4) := by
    have h : (R : ℝ) ^ ((3 : ℝ) / 4) ≤ (R' : ℝ) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hR0 hRR (by norm_num)
    exact mul_le_mul hSS h (by positivity) hS'0
  have hlast : ((D : ℝ)⁻¹ * ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)
        + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
        * (((R : ℝ) * (S : ℝ)) ^ ε)
      ≤ ((D : ℝ)⁻¹ * ((R' : ℝ) * (S' : ℝ)) ^ ((3 : ℝ) / 2)
        + (R' : ℝ) * (S' : ℝ) ^ ((3 : ℝ) / 4) + (S' : ℝ) * (R' : ℝ) ^ ((3 : ℝ) / 4))
        * (((R' : ℝ) * (S' : ℝ)) ^ ε) :=
    mul_le_mul (by linarith) heps (Real.rpow_nonneg hRS0 _) (by positivity)
  unfold Work.FIArea4.p14T12
  linarith [hmid, hlast]

end

end Work.FIArea4.Vflip
