import Mathlib
import Submission.Work.DSM4p.Chart
import Submission.Work.DSM4p.ChartUnit
import Submission.Work.DSM4p.isReduced_perfectRing
import Submission.Work.DSM4p.exists_eq_algebraMap_of_pow_pow
import Submission.Work.DSM4p.chartLevel_exists_aeval

/-!
# `Work.DSM4p.kerP` — the characteristic-`p` kernel estimate

This file proves the characteristic-`p` kernel estimate of the Riemann extension tower
(`sources/dsmap/M4pU.lean`, node `kerP`, the "Route U" of `Submission/Work/DSM4p/Main.lean`):

for a perfect ring `R` of characteristic `p`, compatible systems `G` (roots of `g = G 0`) and
`T` (the pseudo-uniformiser) with `T 0` a nonzerodivisor, and `x : R` whose image in the
`N`-th chart level `D N = chartLevel hG T N ⊆ R[1/G 0]` is divisible by `T 0 ^ M`, one has

  `T (k+1) * G (k+1) * x ∈ (T 0 ^ M)`   whenever   `M * p ^ (k+2) ≤ N`.

## The structure of the proof

Write `a_κ = chartGen hG T N κ = T κ ^ N / G κ` for the generators of the level (the *level* is
`N`, the *index* is `κ`), `π = T κ ^ N`, `γ = G κ`, so that `π = a_κ γ`
(`chartGen_mul_gr`).  The proof has three steps.

1. **The core two-chart estimate** (`hartogs_core`).  For `z` a polynomial in `a := a_κ` of
   degree `≤ P.natDegree` with `z * a ^ B = algebraMap c`, one shows
   `z ^ n * a ^ (2A) ∈ range (algebraMap R _)` for every `n`, where `A = max P.natDegree B`:
   the ideal `I = span {π ^ i γ ^ (2A-i)}` of `R` satisfies `z * alg(I) ⊆ alg(I)` — the case
   `i ≥ B` uses the expression `z = c a^(-B)`, the case `i < B` the polynomial expression for
   `z` — and `alg (π ^ (2A)) ∈ alg I`.  Taking `n = p ^ J` and `p ^ J`-th roots produces
   `T (k+1) z`.

2. **Two-chart Hartogs** (`hartogs`).  Here `z = G (k+1) * y` with `y` an element of the
   `N`-th chart level whose image in `R[1/G 0]` satisfies `T 0 ^ M * y = algebraMap x`: then
   `z` is a polynomial in a *single* generator `a_κ` of a sufficiently high level
   (`chartLevel_exists_aeval`, using the Frobenius structure `a_i = a_κ ^ p^(κ-i)` of the
   chart), and the hypothesis gives an exact expression `z * a_κ ^ B = algebraMap c` with
   `B = p ^ (κ-(k+1))` and `c = x * T κ ^ (N B - M p ^ κ)`.

3. **Assembly** (`kerP`): apply step 2 to `y ^ p` and `x ^ p` (which needs
   `N ≥ M p ^ (k+2)`), multiply the resulting relation by `G (k+1) ^ (p-1)` — which kills the
   `Ann (G 0)`-torsion of `R[1/G 0]` — and take `p`-th roots in the perfect ring `R`.

## Contents

* `Work.DSM4p.hartogs_core` — the core two-chart estimate;
* `Work.DSM4p.kerP` — the node.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.DSM4p

universe a

section Core

variable {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]
variable {G T : ℕ → R}

/-- **The two-chart core estimate.**  Let `z` be a polynomial in the level-`N` chart generator
`a = chartGen hG T N κ` of degree `P.natDegree` whose product with `a ^ B` is the image of an
element `c` of `R`; suppose moreover that the image of `R` in the ambient ring is closed under
`p ^ J`-th roots (`hroot`; provided by `Work.DSM4p.exists_eq_algebraMap_of_pow_pow`).

Then `T (k+1) * z` is again the image of an element of `R`, for any index `κ ≥ k+1`. -/
theorem hartogs_core (hG : IsRootSystem p G) (hT : IsRootSystem p T)
    {k κ N B : ℕ} (hκ : k + 1 ≤ κ) {z : ChartAmbient G} (P : Polynomial R)
    (hz : z = Polynomial.aeval (chartGen hG T N κ) P) (c : R)
    (hc : z * (chartGen hG T N κ) ^ B = algebraMap R (ChartAmbient G) c)
    (hroot : ∀ {J : ℕ} {u : ChartAmbient G} {σ : R},
      u ^ p ^ J = algebraMap R (ChartAmbient G) σ →
        ∃ τ : R, u = algebraMap R (ChartAmbient G) τ) :
    ∃ τ : R, algebraMap R (ChartAmbient G) (T (k + 1)) * z =
      algebraMap R (ChartAmbient G) τ := by
  classical
  have rpow : ∀ {r : ℕ → R} (hr : IsRootSystem p r) {a b : ℕ}, a ≤ b → r b ^ p ^ (b - a) = r a := by
    intro r hr a b hab
    rw [← Nat.add_sub_cancel' hab, Nat.add_sub_cancel_left]
    exact hr.pow_pow a (b - a)
  set A : ℕ := max P.natDegree B with hAdef
  have hA1 : P.natDegree ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hA2 : B ≤ A := by rw [hAdef]; exact le_max_right _ _
  set a : ChartAmbient G := chartGen hG T N κ with ha
  set u : (ChartAmbient G)ˣ := chartUnit hG κ with hu_def
  have hu : (↑u : ChartAmbient G) = algebraMap R (ChartAmbient G) (G κ) := chartUnit_val hG κ
  have hau : a * (↑u : ChartAmbient G) = algebraMap R (ChartAmbient G) (T κ ^ N) := by
    rw [ha, mul_comm]; exact chartUnit_mul_chartGen hG T N κ
  have hup : ∀ m : ℕ, (↑(u ^ m) : ChartAmbient G) = algebraMap R (ChartAmbient G) (G κ ^ m) := by
    intro m; rw [Units.val_pow_eq_pow_val, hu, ← map_pow]
  have k1 : ∀ i : ℕ, a ^ i * (↑u : ChartAmbient G) ^ i =
      algebraMap R (ChartAmbient G) (T κ ^ (N * i)) := by
    intro i; rw [← mul_pow, hau, ← map_pow, ← pow_mul]
  have k2 : ∀ i : ℕ, i ≤ 2 * A → a ^ i * (↑u : ChartAmbient G) ^ (2 * A) =
      algebraMap R (ChartAmbient G) (T κ ^ (N * i) * G κ ^ (2 * A - i)) := by
    intro i hi
    calc a ^ i * (↑u : ChartAmbient G) ^ (2 * A)
        = a ^ i * ((↑u : ChartAmbient G) ^ i * (↑u : ChartAmbient G) ^ (2 * A - i)) := by
            rw [← pow_add, Nat.add_sub_cancel' hi]
      _ = (a ^ i * (↑u : ChartAmbient G) ^ i) * (↑u : ChartAmbient G) ^ (2 * A - i) := by
            rw [mul_assoc]
      _ = algebraMap R (ChartAmbient G) (T κ ^ (N * i)) * (↑u : ChartAmbient G) ^ (2 * A - i) := by
            rw [k1 i]
      _ = algebraMap R (ChartAmbient G) (T κ ^ (N * i)) *
            algebraMap R (ChartAmbient G) (G κ ^ (2 * A - i)) := by
            rw [← Units.val_pow_eq_pow_val, hup]
      _ = algebraMap R (ChartAmbient G) (T κ ^ (N * i) * G κ ^ (2 * A - i)) := by rw [map_mul]
  set gen : Fin (2 * A + 1) → R := fun i => T κ ^ (N * (i : ℕ)) * G κ ^ (2 * A - (i : ℕ)) with hgen
  set I : Ideal R := Ideal.span (Set.range gen) with hI
  have hgi_all : ∀ i : Fin (2 * A + 1),
      algebraMap R (ChartAmbient G) (gen i) = a ^ (i : ℕ) * (↑u : ChartAmbient G) ^ (2 * A) := by
    intro i
    rw [show gen i = T κ ^ (N * (i : ℕ)) * G κ ^ (2 * A - (i : ℕ)) from rfl,
      ← k2 (i : ℕ) (by omega)]
  have key : ∀ i : Fin (2 * A + 1),
      ∃ η ∈ I, z * algebraMap R (ChartAmbient G) (gen i) = algebraMap R (ChartAmbient G) η := by
    intro i
    by_cases hiB : B ≤ (i : ℕ)
    · refine ⟨c * (T κ ^ (N * ((i : ℕ) - B)) * G κ ^ (2 * A - ((i : ℕ) - B))), ?_, ?_⟩
      · refine Ideal.mul_mem_left I c ?_
        have h1 : gen (⟨(i : ℕ) - B, by omega⟩ : Fin (2 * A + 1)) ∈ I := by
          rw [hI]; exact Ideal.subset_span (Set.mem_range_self _)
        simpa [hgen] using h1
      · have hpoweq : a ^ (i : ℕ) = a ^ B * a ^ ((i : ℕ) - B) := by
          rw [← pow_add, Nat.add_sub_cancel' hiB]
        calc z * algebraMap R (ChartAmbient G) (gen i)
            = z * (a ^ (i : ℕ) * (↑u : ChartAmbient G) ^ (2 * A)) := by rw [hgi_all i]
          _ = z * ((a ^ B * a ^ ((i : ℕ) - B)) * (↑u : ChartAmbient G) ^ (2 * A)) := by
                rw [hpoweq]
          _ = (z * a ^ B) * (a ^ ((i : ℕ) - B) * (↑u : ChartAmbient G) ^ (2 * A)) := by ring
          _ = algebraMap R (ChartAmbient G) c *
                (a ^ ((i : ℕ) - B) * (↑u : ChartAmbient G) ^ (2 * A)) := by rw [hc]
          _ = algebraMap R (ChartAmbient G)
                (c * (T κ ^ (N * ((i : ℕ) - B)) * G κ ^ (2 * A - ((i : ℕ) - B)))) := by
                rw [k2 ((i : ℕ) - B) (by omega), ← map_mul]
    · have hzP : z = ∑ j ∈ Finset.range (P.natDegree + 1),
          algebraMap R (ChartAmbient G) (P.coeff j) * a ^ j := by
        rw [hz, Polynomial.aeval_eq_sum_range]
        exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def]
      refine ⟨∑ j ∈ Finset.range (P.natDegree + 1),
        P.coeff j * (T κ ^ (N * ((i : ℕ) + j)) * G κ ^ (2 * A - ((i : ℕ) + j))), ?_, ?_⟩
      · refine Ideal.sum_mem I ?_
        intro j hj
        have hjle : j ≤ P.natDegree := by have := Finset.mem_range.mp hj; omega
        refine Ideal.mul_mem_left I _ ?_
        have h1 : gen (⟨(i : ℕ) + j, by omega⟩ : Fin (2 * A + 1)) ∈ I := by
          rw [hI]; exact Ideal.subset_span (Set.mem_range_self _)
        simpa [hgen] using h1
      · rw [hzP, Finset.sum_mul, map_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjle : j ≤ P.natDegree := by have := Finset.mem_range.mp hj; omega
        have hsum : (i : ℕ) + j ≤ 2 * A := by omega
        have hpowstep : a ^ j * (a ^ (i : ℕ) * (↑u : ChartAmbient G) ^ (2 * A)) =
            a ^ ((i : ℕ) + j) * (↑u : ChartAmbient G) ^ (2 * A) := by
          rw [← mul_assoc, ← pow_add, Nat.add_comm j (i : ℕ)]
        calc algebraMap R (ChartAmbient G) (P.coeff j) * a ^ j *
              algebraMap R (ChartAmbient G) (gen i)
            = algebraMap R (ChartAmbient G) (P.coeff j) *
                (a ^ j * (a ^ (i : ℕ) * (↑u : ChartAmbient G) ^ (2 * A))) := by
                rw [hgi_all i]; ring
          _ = algebraMap R (ChartAmbient G) (P.coeff j) *
                (a ^ ((i : ℕ) + j) * (↑u : ChartAmbient G) ^ (2 * A)) := by rw [hpowstep]
          _ = algebraMap R (ChartAmbient G) (P.coeff j) *
                algebraMap R (ChartAmbient G)
                  (T κ ^ (N * ((i : ℕ) + j)) * G κ ^ (2 * A - ((i : ℕ) + j))) := by
                rw [k2 ((i : ℕ) + j) (by omega)]
          _ = algebraMap R (ChartAmbient G)
                (P.coeff j * (T κ ^ (N * ((i : ℕ) + j)) * G κ ^ (2 * A - ((i : ℕ) + j)))) := by
                simp only [map_mul]
  have hcl : ∀ r ∈ I, ∃ η ∈ I, z * algebraMap R (ChartAmbient G) r =
      algebraMap R (ChartAmbient G) η := by
    intro r hr
    rw [hI] at hr
    refine Submodule.span_induction (p := fun r _ => ∃ η ∈ I,
      z * algebraMap R (ChartAmbient G) r = algebraMap R (ChartAmbient G) η) ?_ ?_ ?_ ?_ hr
    · rintro x ⟨i, rfl⟩
      exact key i
    · exact ⟨0, I.zero_mem, by simp⟩
    · rintro x y hx hy ⟨η₁, h1, e1⟩ ⟨η₂, h2, e2⟩
      exact ⟨η₁ + η₂, I.add_mem h1 h2, by rw [map_add, mul_add, map_add, e1, e2]⟩
    · rintro a' x hx ⟨η, h, e⟩
      refine ⟨a' * η, I.mul_mem_left a' h, ?_⟩
      rw [smul_eq_mul, map_mul, map_mul]
      rw [show z * ((algebraMap R (ChartAmbient G) a') * (algebraMap R (ChartAmbient G) x)) =
          (algebraMap R (ChartAmbient G) a') * (z * (algebraMap R (ChartAmbient G) x)) by ring, e]
  have hind : ∀ n : ℕ, ∃ η ∈ I, z ^ n * algebraMap R (ChartAmbient G) (T κ ^ (N * (2 * A))) =
      algebraMap R (ChartAmbient G) η := by
    intro n
    induction n with
    | zero =>
        refine ⟨gen (⟨2 * A, by omega⟩ : Fin (2 * A + 1)), ?_, ?_⟩
        · rw [hI]; exact Ideal.subset_span (Set.mem_range_self _)
        · simp only [pow_zero, one_mul]
          rw [show gen (⟨2 * A, by omega⟩ : Fin (2 * A + 1)) =
              T κ ^ (N * (2 * A)) * G κ ^ (2 * A - 2 * A) from rfl,
            Nat.sub_self, pow_zero, mul_one]
    | succ n ih =>
        obtain ⟨η, hη, he⟩ := ih
        obtain ⟨η', hη', he'⟩ := hcl η hη
        refine ⟨η', hη', ?_⟩
        have h2 : z ^ n * (z * algebraMap R (ChartAmbient G) (T κ ^ (N * (2 * A)))) =
            z * (z ^ n * algebraMap R (ChartAmbient G) (T κ ^ (N * (2 * A)))) := by ring
        rw [pow_succ, mul_assoc, h2, he, he']
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, 2 * A * N ≤ p ^ (κ + J - (k + 1)) :=
    ⟨2 * A * N + (k + 1), by
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      have h1 : 2 * A * N < p ^ (2 * A * N) := Nat.lt_pow_self (n := 2 * A * N) (a := p) hp1
      have h2 : p ^ (2 * A * N) ≤ p ^ (κ + (2 * A * N + (k + 1)) - (k + 1)) :=
        Nat.pow_le_pow_right (le_of_lt hp1) (by omega)
      omega⟩
  obtain ⟨η, hη, he⟩ := hind (p ^ J)
  have hTpow : (T (κ + J)) ^ p ^ J = T κ := by
    have h := rpow hT (a := κ) (b := κ + J) (by omega)
    rwa [Nat.add_sub_cancel_left] at h
  have hmul : ((T (κ + J)) ^ (2 * A * N)) ^ p ^ J = ((T (κ + J)) ^ p ^ J) ^ (2 * A * N) := by
    conv_lhs => rw [← pow_mul]
    conv_rhs => rw [← pow_mul]
    rw [Nat.mul_comm]
  have hpow : (z * algebraMap R (ChartAmbient G) ((T (κ + J)) ^ (2 * A * N))) ^ p ^ J =
      algebraMap R (ChartAmbient G) η := by
    rw [mul_pow, ← map_pow, hmul, hTpow, show 2 * A * N = N * (2 * A) from by ring]
    exact he
  obtain ⟨τ, hτ⟩ := hroot hpow
  refine ⟨(T (κ + J)) ^ (p ^ (κ + J - (k + 1)) - 2 * A * N) * τ, ?_⟩
  have hTk : T (k + 1) = (T (κ + J)) ^ p ^ (κ + J - (k + 1)) := by
    rw [show T (k + 1) = T κ ^ p ^ (κ - (k + 1)) from
          (rpow hT (a := k + 1) (b := κ) (by omega)).symm,
        show T κ = (T (κ + J)) ^ p ^ J from hTpow.symm, ← pow_mul, ← pow_add,
        show J + (κ - (k + 1)) = κ + J - (k + 1) from by omega]
  have hexp : p ^ (κ + J - (k + 1)) =
      (p ^ (κ + J - (k + 1)) - 2 * A * N) + 2 * A * N := (Nat.sub_add_cancel hJ).symm
  calc algebraMap R (ChartAmbient G) (T (k + 1)) * z
      = algebraMap R (ChartAmbient G) ((T (κ + J)) ^ p ^ (κ + J - (k + 1))) * z := by rw [hTk]
    _ = algebraMap R (ChartAmbient G)
          (((T (κ + J)) ^ (p ^ (κ + J - (k + 1)) - 2 * A * N)) * ((T (κ + J)) ^ (2 * A * N))) *
          z := by
          rw [show (T (κ + J)) ^ p ^ (κ + J - (k + 1)) =
              ((T (κ + J)) ^ (p ^ (κ + J - (k + 1)) - 2 * A * N)) *
                ((T (κ + J)) ^ (2 * A * N)) from by
            conv_lhs => rw [hexp, pow_add]]
    _ = (algebraMap R (ChartAmbient G) ((T (κ + J)) ^ (p ^ (κ + J - (k + 1)) - 2 * A * N)) *
          algebraMap R (ChartAmbient G) ((T (κ + J)) ^ (2 * A * N))) * z := by rw [map_mul]
    _ = algebraMap R (ChartAmbient G) ((T (κ + J)) ^ (p ^ (κ + J - (k + 1)) - 2 * A * N)) *
          (z * algebraMap R (ChartAmbient G) ((T (κ + J)) ^ (2 * A * N))) := by ring
    _ = algebraMap R (ChartAmbient G) ((T (κ + J)) ^ (p ^ (κ + J - (k + 1)) - 2 * A * N)) *
          algebraMap R (ChartAmbient G) τ := by rw [hτ]
    _ = algebraMap R (ChartAmbient G)
          (((T (κ + J)) ^ (p ^ (κ + J - (k + 1)) - 2 * A * N)) * τ) := by rw [map_mul]

/-- **Two-chart Hartogs.**  Let `y` be an element of the `N`-th chart level whose image in
`R[1/G 0]` satisfies `y * T 0 ^ M = algebraMap x`, and suppose `N ≥ M * p ^ (k+1)`.  Then
`T (k+1) * G (k+1) * y` is the image of an element of `R`. -/
theorem hartogs (hG : IsRootSystem p G) (hT : IsRootSystem p T)
    {k M N : ℕ} (hN : M * p ^ (k + 1) ≤ N) {y : chartLevel hG T N} {x : R}
    (hy : (y : ChartAmbient G) * algebraMap R (ChartAmbient G) (T 0 ^ M) =
      algebraMap R (ChartAmbient G) x) :
    ∃ τ : R, algebraMap R (ChartAmbient G) (T (k + 1)) *
        (algebraMap R (ChartAmbient G) (G (k + 1)) * (y : ChartAmbient G)) =
      algebraMap R (ChartAmbient G) τ := by
  classical
  have rpow : ∀ {r : ℕ → R} (hr : IsRootSystem p r) {a b : ℕ}, a ≤ b → r b ^ p ^ (b - a) = r a := by
    intro r hr a b hab
    rw [← Nat.add_sub_cancel' hab, Nat.add_sub_cancel_left]
    exact hr.pow_pow a (b - a)
  obtain ⟨κ, hκ, P, hP⟩ := chartLevel_exists_aeval hG hT (N := N) (k + 1) y
  set B : ℕ := p ^ (κ - (k + 1)) with hBdef
  set c : R := x * T κ ^ (N * B - M * p ^ κ) with hcdef
  have hBpow : (chartUnit hG κ) ^ B = chartUnit hG (k + 1) := chartUnit_pow_pow hG hκ
  have haB : (chartGen hG T N κ) ^ B =
      algebraMap R (ChartAmbient G) (T κ ^ (N * B)) *
        (↑(((chartUnit hG κ) ^ B)⁻¹) : ChartAmbient G) := chartGen_pow_eq hG T N κ B
  have hv : (↑(chartUnit hG (k + 1)) : ChartAmbient G) =
      algebraMap R (ChartAmbient G) (G (k + 1)) := chartUnit_val hG (k + 1)
  have hbinv : (↑(chartUnit hG (k + 1)) : ChartAmbient G) *
      (↑((chartUnit hG (k + 1))⁻¹) : ChartAmbient G) = 1 := by
    rw [← Units.val_mul,
      show chartUnit hG (k + 1) * (chartUnit hG (k + 1))⁻¹ = (1 : (ChartAmbient G)ˣ) from
        mul_inv_cancel _, Units.val_one]
  have hcancel : ∀ X : ChartAmbient G,
      (↑(chartUnit hG (k + 1)) : ChartAmbient G) *
        (X * (↑((chartUnit hG (k + 1))⁻¹) : ChartAmbient G)) = X := by
    intro X
    rw [← mul_assoc, mul_comm (↑(chartUnit hG (k + 1)) : ChartAmbient G) X, mul_assoc, hbinv,
      mul_one]
  have hb : M * p ^ κ ≤ N * B := by
    have h1 : M * p ^ κ = (M * p ^ (k + 1)) * B := by
      rw [hBdef, mul_assoc, ← pow_add, Nat.add_sub_cancel' hκ]
    rw [h1]
    exact Nat.mul_le_mul_right _ hN
  have hTκ : T κ ^ p ^ κ = T 0 := by
    have h := rpow hT (a := 0) (b := κ) (Nat.zero_le κ)
    rwa [Nat.sub_zero] at h
  have hTzero : (T 0) ^ M = T κ ^ (M * p ^ κ) := by
    rw [← hTκ, ← pow_mul, Nat.mul_comm]
  have hkey1 : (y : ChartAmbient G) * algebraMap R (ChartAmbient G) (T κ ^ (N * B)) =
      algebraMap R (ChartAmbient G) c := by
    have h1 : algebraMap R (ChartAmbient G) (T 0 ^ M) *
        algebraMap R (ChartAmbient G) (T κ ^ (N * B - M * p ^ κ)) =
        algebraMap R (ChartAmbient G) (T κ ^ (N * B)) := by
      rw [← map_mul, hTzero, ← pow_add,
        show M * p ^ κ + (N * B - M * p ^ κ) = N * B from by omega]
    calc (y : ChartAmbient G) * algebraMap R (ChartAmbient G) (T κ ^ (N * B))
        = (y : ChartAmbient G) * (algebraMap R (ChartAmbient G) (T 0 ^ M) *
            algebraMap R (ChartAmbient G) (T κ ^ (N * B - M * p ^ κ))) := by rw [h1]
      _ = ((y : ChartAmbient G) * algebraMap R (ChartAmbient G) (T 0 ^ M)) *
            algebraMap R (ChartAmbient G) (T κ ^ (N * B - M * p ^ κ)) := by ring
      _ = algebraMap R (ChartAmbient G) x *
            algebraMap R (ChartAmbient G) (T κ ^ (N * B - M * p ^ κ)) := by rw [hy]
      _ = algebraMap R (ChartAmbient G) c := by rw [← map_mul, hcdef]
  have hz : algebraMap R (ChartAmbient G) (G (k + 1)) * (y : ChartAmbient G) =
      Polynomial.aeval (chartGen hG T N κ) (Polynomial.C (G (k + 1)) * P) := by
    rw [map_mul, Polynomial.aeval_C, hP]
  have hc : (algebraMap R (ChartAmbient G) (G (k + 1)) * (y : ChartAmbient G)) *
      (chartGen hG T N κ) ^ B = algebraMap R (ChartAmbient G) c := by
    calc (algebraMap R (ChartAmbient G) (G (k + 1)) * (y : ChartAmbient G)) *
          (chartGen hG T N κ) ^ B
        = ((↑(chartUnit hG (k + 1)) : ChartAmbient G) * (y : ChartAmbient G)) *
            (algebraMap R (ChartAmbient G) (T κ ^ (N * B)) *
              (↑(((chartUnit hG κ) ^ B)⁻¹) : ChartAmbient G)) := by
            rw [← hv, haB]
      _ = ((↑(chartUnit hG (k + 1)) : ChartAmbient G) * (y : ChartAmbient G)) *
            (algebraMap R (ChartAmbient G) (T κ ^ (N * B)) *
              (↑((chartUnit hG (k + 1))⁻¹) : ChartAmbient G)) := by rw [hBpow]
      _ = (y : ChartAmbient G) * algebraMap R (ChartAmbient G) (T κ ^ (N * B)) := by
            rw [show ((↑(chartUnit hG (k + 1)) : ChartAmbient G) * (y : ChartAmbient G)) *
                  (algebraMap R (ChartAmbient G) (T κ ^ (N * B)) *
                    (↑((chartUnit hG (k + 1))⁻¹) : ChartAmbient G)) =
                (↑(chartUnit hG (k + 1)) : ChartAmbient G) *
                  (((y : ChartAmbient G) * algebraMap R (ChartAmbient G) (T κ ^ (N * B))) *
                    (↑((chartUnit hG (k + 1))⁻¹) : ChartAmbient G)) from by ring,
              hcancel]
      _ = algebraMap R (ChartAmbient G) c := hkey1
  exact hartogs_core hG hT hκ (Polynomial.C (G (k + 1)) * P) hz c hc
    (fun h => exists_eq_algebraMap_of_pow_pow (f := G 0) h)

end Core

theorem kerP {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]
    {G T : ℕ → R} (hG : Work.DSM4p.IsRootSystem p G) (hT : Work.DSM4p.IsRootSystem p T)
    (hT0 : IsSMulRegular R (T 0)) (k M N : ℕ) (hN : M * p ^ (k + 2) ≤ N) (x : R)
    (hx : algebraMap R (Work.DSM4p.chartRing hG T N) x ∈
      Ideal.span {(algebraMap R (Work.DSM4p.chartRing hG T N) (T 0)) ^ M}) :
    T (k + 1) * G (k + 1) * x ∈ Ideal.span {T 0 ^ M} := by
  classical
  have hred : IsReduced R := isReduced_perfectRing
  have pow_p_inj : ∀ {u v : R}, u ^ p = v ^ p → u = v :=
    fun h => PerfectRing.bijective_frobenius.injective h
  have pow_pow_inj : ∀ (n : ℕ) {u v : R}, u ^ p ^ n = v ^ p ^ n → u = v := by
    intro n
    induction n with
    | zero => intro u v h; simpa using h
    | succ n ih =>
        intro u v h
        refine ih (pow_p_inj ?_)
        simpa [pow_succ, pow_mul] using h
  have hnil : ∀ x : R, ∀ m : ℕ, x ^ m = 0 → x = 0 := by
    intro x m hm
    obtain ⟨s, hs⟩ : ∃ s, m ≤ p ^ s :=
      ⟨m, le_of_lt (Nat.lt_pow_self (n := m) (a := p) (Fact.out : p.Prime).one_lt)⟩
    have h1 : x ^ p ^ s = 0 := by
      rw [show p ^ s = m + (p ^ s - m) from (Nat.add_sub_cancel' hs).symm, pow_add, hm, zero_mul]
    exact pow_pow_inj s (by rw [h1, zero_pow (pow_ne_zero s (Fact.out : p.Prime).ne_zero)])
  -- (1) the hypothesis, as an equation in the ambient ring `R[1/G 0]`
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
  have hyC : (y : ChartAmbient G) * algebraMap R (ChartAmbient G) (T 0 ^ M) =
      algebraMap R (ChartAmbient G) x := by
    have h := congrArg (Subalgebra.val (chartLevel hG T N)) hy
    simpa using h
  -- (2) the Hartogs estimate applied to `y ^ p` and `x ^ p`
  have hyP : ((y ^ p : chartLevel hG T N) : ChartAmbient G) *
      algebraMap R (ChartAmbient G) (T 0 ^ (M * p)) =
      algebraMap R (ChartAmbient G) (x ^ p) := by
    have h1 : ((y ^ p : chartLevel hG T N) : ChartAmbient G) = (y : ChartAmbient G) ^ p := by
      change (Subalgebra.val (chartLevel hG T N)) (y ^ p) =
        ((Subalgebra.val (chartLevel hG T N)) y) ^ p
      rw [map_pow]
    have h2 : algebraMap R (ChartAmbient G) (T 0 ^ (M * p)) =
        (algebraMap R (ChartAmbient G) (T 0 ^ M)) ^ p := by rw [pow_mul, ← map_pow]
    have h3 : algebraMap R (ChartAmbient G) (x ^ p) =
        (algebraMap R (ChartAmbient G) x) ^ p := by rw [map_pow]
    rw [h1, h2, h3, ← mul_pow, hyC]
  have hN' : M * p * p ^ (k + 1) ≤ N := by
    have h1 : M * p * p ^ (k + 1) = M * p ^ (k + 2) := by rw [mul_assoc, ← pow_succ']
    rw [h1]; exact hN
  obtain ⟨τ, hτ⟩ := hartogs hG hT (k := k) (M := M * p) (N := N) hN' (y := y ^ p)
    (x := x ^ p) hyP
  -- (3) the relation `Δ := T (k+1) G (k+1) x^p - (T 0)^(Mp) τ` lies in `Ann (G 0)`
  have hxpow : algebraMap R (ChartAmbient G) (x ^ p) =
      algebraMap R (ChartAmbient G) ((T 0) ^ (M * p)) *
        ((y ^ p : chartLevel hG T N) : ChartAmbient G) := by
    rw [← hyP]; ring
  have hrel : algebraMap R (ChartAmbient G) (T (k + 1) * G (k + 1) * x ^ p) =
      algebraMap R (ChartAmbient G) ((T 0) ^ (M * p) * τ) := by
    calc algebraMap R (ChartAmbient G) (T (k + 1) * G (k + 1) * x ^ p)
        = algebraMap R (ChartAmbient G) (T (k + 1)) *
            (algebraMap R (ChartAmbient G) (G (k + 1)) *
              algebraMap R (ChartAmbient G) (x ^ p)) := by
            rw [map_mul, map_mul]; ring
      _ = algebraMap R (ChartAmbient G) (T (k + 1)) *
            (algebraMap R (ChartAmbient G) (G (k + 1)) *
              (algebraMap R (ChartAmbient G) ((T 0) ^ (M * p)) *
                ((y ^ p : chartLevel hG T N) : ChartAmbient G))) := by rw [hxpow]
      _ = algebraMap R (ChartAmbient G) ((T 0) ^ (M * p)) *
            (algebraMap R (ChartAmbient G) (T (k + 1)) *
              (algebraMap R (ChartAmbient G) (G (k + 1)) *
                ((y ^ p : chartLevel hG T N) : ChartAmbient G))) := by ring
      _ = algebraMap R (ChartAmbient G) ((T 0) ^ (M * p)) * algebraMap R (ChartAmbient G) τ := by
            rw [hτ]
      _ = algebraMap R (ChartAmbient G) ((T 0) ^ (M * p) * τ) := by rw [map_mul]
  have hann : G 0 * (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) = 0 := by
    have hker : algebraMap R (ChartAmbient G)
        (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) = 0 := by
      rw [map_sub, hrel, sub_self]
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (x := G 0) (S := ChartAmbient G)
      (a := T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) (b := 0)
      (by rw [hker, map_zero])
    have hn' : (G 0) ^ n * (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) = 0 := by
      simpa using hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [pow_zero, one_mul] at hn'
      rw [hn', mul_zero]
    · have hz : (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) ^ n =
          (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) ^ (n - 1) *
            (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) := by
        rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n from hpos)]
      refine hnil _ n ?_
      rw [mul_pow, hz,
        show (G 0) ^ n * ((T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) ^ (n - 1) *
            (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ)) =
          ((G 0) ^ n * (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ)) *
            (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) ^ (n - 1) from by ring,
        hn', zero_mul]
  -- `G (k+1)` kills `Ann (G 0)`
  have hGi : G (k + 1) * (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) = 0 := by
    have hG0 : (G (k + 1)) ^ p ^ (k + 1) = G 0 := by
      have h := (IsRootSystem.pow_pow hG 0 (k + 1))
      simpa using h
    have hpow : ((G (k + 1)) * (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ)) ^
        p ^ (k + 1) = 0 := by
      have h1 : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      rw [mul_pow, hG0,
        show (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) ^ p ^ (k + 1) =
          (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) *
            (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) ^ (p ^ (k + 1) - 1) from by
          rw [← pow_succ', Nat.sub_add_cancel h1]]
      rw [← mul_assoc, hann, zero_mul]
    have h2 : ((G (k + 1)) * (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ)) ^
        p ^ (k + 1) = (0 : R) ^ p ^ (k + 1) := by
      rw [hpow, zero_pow (pow_ne_zero (k + 1) (Fact.out : p.Prime).ne_zero)]
    exact pow_pow_inj (k + 1) h2
  -- multiply by `T (k+1) ^ (p-1) G (k+1) ^ (p-1)`
  have hkill : ((T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) *
      ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1))) = 0 := by
    have hp1 : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
    have hT1 : (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) *
        (G (k + 1)) ^ (p - 1) = 0 := by
      have hsplit : (G (k + 1)) ^ (p - 1) = (G (k + 1)) ^ (p - 1 - 1) * G (k + 1) := by
        conv_lhs => rw [show p - 1 = (p - 1 - 1) + 1 from (Nat.sub_add_cancel hp1).symm]
        rw [pow_add, pow_one]
      rw [hsplit,
        show (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) *
            ((G (k + 1)) ^ (p - 1 - 1) * G (k + 1)) =
          ((T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) * G (k + 1)) *
            (G (k + 1)) ^ (p - 1 - 1) from by ring,
        mul_comm (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) (G (k + 1)),
        hGi, zero_mul]
    calc (T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) *
          ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1))
        = ((T (k + 1) * G (k + 1) * x ^ p - (T 0) ^ (M * p) * τ) * (G (k + 1)) ^ (p - 1)) *
            (T (k + 1)) ^ (p - 1) := by ring
      _ = 0 := by rw [hT1, zero_mul]
  have hEq : (T (k + 1) * G (k + 1) * x ^ p) *
        ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1)) =
      ((T 0) ^ (M * p) * τ) * ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1)) := by
    have h2 : (T (k + 1) * G (k + 1) * x ^ p) *
          ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1)) -
        ((T 0) ^ (M * p) * τ) * ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1)) = 0 := by
      rw [← sub_mul]; exact hkill
    exact sub_eq_zero.mp h2
  -- take `p`-th roots
  have hTp : (T (k + 1)) ^ p = T (k + 1) * (T (k + 1)) ^ (p - 1) := by
    conv_lhs => rw [show p = (p - 1) + 1 from
      (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm]
    rw [pow_succ, mul_comm]
  have hGp : (G (k + 1)) ^ p = G (k + 1) * (G (k + 1)) ^ (p - 1) := by
    conv_lhs => rw [show p = (p - 1) + 1 from
      (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm]
    rw [pow_succ, mul_comm]
  have hpth : (T (k + 1) * G (k + 1) * x) ^ p =
      (T 0) ^ (M * p) *
        (τ * ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1))) := by
    calc (T (k + 1) * G (k + 1) * x) ^ p
        = (T (k + 1) * G (k + 1) * x ^ p) *
            ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1)) := by
          rw [mul_pow, mul_pow, hTp, hGp]; ring
      _ = ((T 0) ^ (M * p) * τ) * ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1)) := hEq
      _ = (T 0) ^ (M * p) *
            (τ * ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1))) := by ring
  obtain ⟨δ, hδ⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p)).2
    (τ * ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1)))
  have hfin : (T (k + 1) * G (k + 1) * x) ^ p = ((T 0) ^ M * δ) ^ p := by
    calc (T (k + 1) * G (k + 1) * x) ^ p
        = (T 0) ^ (M * p) *
            (τ * ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1))) := hpth
      _ = (T 0) ^ (M * p) * δ ^ p := by
            rw [show δ ^ p = τ * ((T (k + 1)) ^ (p - 1) * (G (k + 1)) ^ (p - 1)) from hδ]
      _ = ((T 0) ^ M) ^ p * δ ^ p := by rw [pow_mul]
      _ = ((T 0) ^ M * δ) ^ p := by rw [mul_pow]
  have hxy : T (k + 1) * G (k + 1) * x = (T 0) ^ M * δ := pow_p_inj hfin
  exact Ideal.mem_span_singleton'.mpr ⟨δ, by rw [hxy]; ring⟩

end Work.DSM4p
