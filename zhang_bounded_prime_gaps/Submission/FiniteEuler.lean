import Mathlib

open scoped BigOperators

/-!
# Finite Euler-product factorization of squarefree double divisor sums

The combinatorial heart of P8 Lemma 4.1 (Polymath8a, "Variants of the Selberg
sieve") steps (39)–(41) and of the per-coordinate evaluation
`Z(F,G) = (1+o(1)) · B⁻¹ · N/φ(N) · ∫₀^∞ F'G'`:

A squarefree divisor `d = ∏_{p∈A} p` of a number with prime set `S` is
encoded by its subset `A ⊆ S`; the lcm of two squarefree divisors `d,d'` is
`∏_{p ∈ A∪B} p`.  For multiplicative values with local (per-prime) weights
`x p, y p, z p` the double divisor sum

    Σ_{A,B ⊆ S} μ(d)μ(d') X(d) Y(d') Z([d,d'])
    = Σ_{A,B ⊆ S} (∏_{p∈A} -x p) (∏_{p∈B} -y p) (∏_{p∈A∪B} z p)

factors into the Euler product `∏_{p∈S} (1 - x p z p - y p z p + x p y p z p)`
(`pairFactor`, the *per-coordinate* case, `k = 1`).

For `k` coordinates with the pairwise-coprime condition on the pair-lcms
(`p` divides at most one `[d_j,d'_j]`) the corresponding factorization has
local factor `1 + Σ_j (−x_jp z_jp − y_jp z_jp + x_jp y_jp z_jp)` — exactly
the `K_p` of P8 (39) (`coordFactor`, in per-prime status encoding).

Everything is pure algebra over a commutative ring `R` (kernel-verified), and
is independent of the analytic campaign (Fourier transforms, modified zeta,
truncation) that builds on these sums.
-/


namespace Commons.NumberTheory.MaynardSieve

section FiniteEuler

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

/-- The per-coordinate double-divisor-summand: for subsets `A, B` of a prime set
(the squarefree divisors `d = ∏_{p∈A} p`, `d' = ∏_{p∈B} p`), the weight
`∏_{p∈A}(-x p) · ∏_{p∈B}(-y p) · ∏_{p∈A∪B} z p` — the image of
`μ(d)μ(d')X(d)Y(d')Z([d,d'])` for multiplicative `X,Y,Z` with local values
`x,y,z` and `[d,d'] = ∏_{p ∈ A∪B} p` (squarefree). -/
noncomputable def pairTerm (x y z : ι → R) (A B : Finset ι) : R :=
  (∏ p ∈ A, -x p) * (∏ p ∈ B, -y p) * (∏ p ∈ A ∪ B, z p)

/-- The per-prime local factor: contributions 1 (p in neither), `-x p z p`
(p only in the first divisor), `-y p z p` (only in the second), and
`x p y p z p` (in both). -/
noncomputable def pairLocal (x y z : ι → R) (p : ι) : R :=
  1 - x p * z p - y p * z p + x p * y p * z p

/-- Single-sum version of the powerset-insert split. -/
lemma sum_powerset_insert {M : Type*} [AddCommMonoid M] (S : Finset ι) (a : ι)
    (ha : a ∉ S) (f : Finset ι → M) :
    (∑ A ∈ (insert a S).powerset, f A) =
      (∑ A ∈ S.powerset, f A) + ∑ A ∈ S.powerset, f (insert a A) := by
  classical
  have hinj : Set.InjOn (insert a) (↑S.powerset : Set (Finset ι)) := by
    intro A hA B hB hEq
    have hAn : a ∉ A := by
      have hAsub : A ⊆ S := Finset.mem_powerset.mp hA
      exact fun hmem => ha (hAsub hmem)
    have hBn : a ∉ B := by
      have hBsub : B ⊆ S := Finset.mem_powerset.mp hB
      exact fun hmem => ha (hBsub hmem)
    have hE := congrArg (fun t : Finset ι => t.erase a) hEq
    simpa [Finset.erase_insert hAn, Finset.erase_insert hBn] using hE
  have hdisj : Disjoint S.powerset (Finset.image (insert a) S.powerset) := by
    rw [Finset.disjoint_left]
    intro P hP hIm
    rcases Finset.mem_image.mp hIm with ⟨P₀, hP₀, rfl⟩
    have hPsub : insert a P₀ ⊆ S := Finset.mem_powerset.mp hP
    exact ha (hPsub (Finset.mem_insert.mpr (Or.inl rfl)))
  rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj]

/-- Block identity: inserting `a` on the first coordinate only. -/
lemma pairTerm_insert_first (x y z : ι → R) (a : ι) {A B : Finset ι}
    (hA : a ∉ A) (hB : a ∉ B) :
    pairTerm x y z (insert a A) B = (-(x a) * z a) * pairTerm x y z A B := by
  classical
  unfold pairTerm
  have hAB : a ∉ A ∪ B := by simp [hA, hB]
  rw [Finset.prod_insert hA]
  have hun : insert a A ∪ B = insert a (A ∪ B) := by
    ext p
    by_cases hpa : p = a <;> simp [hpa, Finset.mem_union, Finset.mem_insert]
  rw [hun, Finset.prod_insert hAB]
  ring

/-- Block identity: inserting `a` on the second coordinate only. -/
lemma pairTerm_insert_second (x y z : ι → R) (a : ι) {A B : Finset ι}
    (hA : a ∉ A) (hB : a ∉ B) :
    pairTerm x y z A (insert a B) = (-(y a) * z a) * pairTerm x y z A B := by
  classical
  unfold pairTerm
  have hAB : a ∉ A ∪ B := by simp [hA, hB]
  rw [Finset.prod_insert hB]
  have hun : A ∪ insert a B = insert a (A ∪ B) := by
    ext p
    by_cases hpa : p = a <;> simp [hpa, Finset.mem_union, Finset.mem_insert]
  rw [hun, Finset.prod_insert hAB]
  ring

/-- Block identity: inserting `a` on both coordinates. -/
lemma pairTerm_insert_both (x y z : ι → R) (a : ι) {A B : Finset ι}
    (hA : a ∉ A) (hB : a ∉ B) :
    pairTerm x y z (insert a A) (insert a B) = (x a * y a * z a) * pairTerm x y z A B := by
  classical
  unfold pairTerm
  have hAB : a ∉ A ∪ B := by simp [hA, hB]
  rw [Finset.prod_insert hA, Finset.prod_insert hB]
  have hun : insert a A ∪ insert a B = insert a (A ∪ B) := by
    ext p
    by_cases hpa : p = a <;> simp [hpa, Finset.mem_union, Finset.mem_insert]
  rw [hun, Finset.prod_insert hAB]
  ring

/-- The powerset-insertion identity: the double sum over subsets of `insert a S`
equals the double sum over subsets of `S` of the sum of the four membership
blocks of `a`. -/
lemma pairDoubleSum_insert {M : Type*} [AddCommMonoid M] (S : Finset ι) (a : ι)
    (ha : a ∉ S) (t : Finset ι → Finset ι → M) :
    (∑ A ∈ (insert a S).powerset, ∑ B ∈ (insert a S).powerset, t A B) =
      ∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
        (t A B + t A (insert a B) + t (insert a A) B + t (insert a A) (insert a B)) := by
  classical
  calc
    (∑ A ∈ (insert a S).powerset, ∑ B ∈ (insert a S).powerset, t A B)
        = (∑ A ∈ S.powerset, ∑ B ∈ (insert a S).powerset, t A B) +
          (∑ A ∈ S.powerset, ∑ B ∈ (insert a S).powerset, t (insert a A) B) := by
            exact sum_powerset_insert S a ha (fun A => ∑ B ∈ (insert a S).powerset, t A B)
    _ = (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, (t A B + t A (insert a B))) +
        (∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
          (t (insert a A) B + t (insert a A) (insert a B))) := by
          congr 1
          · calc
              (∑ A ∈ S.powerset, ∑ B ∈ (insert a S).powerset, t A B)
                  = ∑ A ∈ S.powerset,
                      ((∑ B ∈ S.powerset, t A B) + (∑ B ∈ S.powerset, t A (insert a B))) := by
                      refine Finset.sum_congr rfl ?_
                      intro A hA
                      exact sum_powerset_insert S a ha (fun B => t A B)
              _ = ∑ A ∈ S.powerset, ∑ B ∈ S.powerset, (t A B + t A (insert a B)) := by
                      apply Finset.sum_congr rfl
                      intro A hA
                      exact (Finset.sum_add_distrib (s := S.powerset)
                        (f := fun B => t A B) (g := fun B => t A (insert a B))).symm
          · calc
              (∑ A ∈ S.powerset, ∑ B ∈ (insert a S).powerset, t (insert a A) B)
                  = ∑ A ∈ S.powerset,
                      ((∑ B ∈ S.powerset, t (insert a A) B) +
                        (∑ B ∈ S.powerset, t (insert a A) (insert a B))) := by
                      refine Finset.sum_congr rfl ?_
                      intro A hA
                      exact sum_powerset_insert S a ha (fun B => t (insert a A) B)
              _ = ∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
                    (t (insert a A) B + t (insert a A) (insert a B)) := by
                      apply Finset.sum_congr rfl
                      intro A hA
                      exact (Finset.sum_add_distrib (s := S.powerset)
                        (f := fun B => t (insert a A) B)
                        (g := fun B => t (insert a A) (insert a B))).symm
    _ = ∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
          (t A B + t A (insert a B) + t (insert a A) B + t (insert a A) (insert a B)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro A hA
          rw [← Finset.sum_add_distrib]
          ac_rfl


/-- The `pairTerm`-specific insertion step: inserting `a` into the prime set
multiplies the whole double sum by the local factor `pairLocal x y z a`. -/
theorem pairTerm_insert_factor (S : Finset ι) (a : ι) (ha : a ∉ S) (x y z : ι → R) :
    (∑ A ∈ (insert a S).powerset, ∑ B ∈ (insert a S).powerset, pairTerm x y z A B) =
      pairLocal x y z a * (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, pairTerm x y z A B) := by
  classical
  calc
    (∑ A ∈ (insert a S).powerset, ∑ B ∈ (insert a S).powerset, pairTerm x y z A B)
        = ∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
            (pairTerm x y z A B + pairTerm x y z A (insert a B) +
              pairTerm x y z (insert a A) B + pairTerm x y z (insert a A) (insert a B)) := by
            exact pairDoubleSum_insert S a ha (fun A B => pairTerm x y z A B)
    _ = ∑ A ∈ S.powerset, ∑ B ∈ S.powerset, pairLocal x y z a * pairTerm x y z A B := by
          refine Finset.sum_congr rfl ?_
          intro A hA
          refine Finset.sum_congr rfl ?_
          intro B hB
          have hAn : a ∉ A := by
            have hAsub : A ⊆ S := Finset.mem_powerset.mp hA
            exact fun hm => ha (hAsub hm)
          have hBn : a ∉ B := by
            have hBsub : B ⊆ S := Finset.mem_powerset.mp hB
            exact fun hm => ha (hBsub hm)
          rw [pairTerm_insert_first x y z a hAn hBn, pairTerm_insert_second x y z a hAn hBn,
            pairTerm_insert_both x y z a hAn hBn]
          unfold pairLocal
          ring
    _ = pairLocal x y z a * (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, pairTerm x y z A B) := by
          calc
            (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, pairLocal x y z a * pairTerm x y z A B)
                = ∑ A ∈ S.powerset, pairLocal x y z a *
                    (∑ B ∈ S.powerset, pairTerm x y z A B) := by
                    refine Finset.sum_congr rfl ?_
                    intro A hA
                    exact (Finset.mul_sum (s := S.powerset)
                      (f := fun B => pairTerm x y z A B) (a := pairLocal x y z a)).symm
            _ = pairLocal x y z a * (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, pairTerm x y z A B) := by
                    exact (Finset.mul_sum (s := S.powerset)
                      (f := fun A => ∑ B ∈ S.powerset, pairTerm x y z A B)
                      (a := pairLocal x y z a)).symm

/-- **Finite Euler-product factorization (per-coordinate form).**  For a finite
set of primes `S` and local values `x, y, z : ι → R`, the double sum over
subsets `A, B ⊆ S` of the squarefree divisor weights
`∏_{p∈A}(-x p) · ∏_{p∈B}(-y p) · ∏_{p∈A∪B} z p` factorizes into the product
over `p ∈ S` of the per-prime local factors
`1 - x p z p - y p z p + x p y p z p`. -/
theorem pairFactor (S : Finset ι) (x y z : ι → R) :
    (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, pairTerm x y z A B) =
      ∏ p ∈ S, pairLocal x y z p := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [pairTerm]
  | insert a S ha ih =>
      calc
        (∑ A ∈ (insert a S).powerset, ∑ B ∈ (insert a S).powerset, pairTerm x y z A B)
            = pairLocal x y z a * (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, pairTerm x y z A B) := by
                exact pairTerm_insert_factor S a ha x y z
        _ = pairLocal x y z a * (∏ p ∈ S, pairLocal x y z p) := by rw [ih]
        _ = ∏ p ∈ insert a S, pairLocal x y z p := by
                rw [Finset.prod_insert ha]

end FiniteEuler

/-! ## k-coordinate (pairwise-coprime) factorization — P8 (39)

For several coordinates `j : Fin k` each carrying its own pair of subsets
(`d_j ↔ A_j`, `d'_j ↔ B_j`), the pairwise-coprime condition on the lcms
`[d_j, d'_j]` means: *at each prime `p` at most one coordinate is active*
(`p` divides at most one `[d_j,d'_j]`).  Encoding per prime the status
`none` (inactive) or `some (j, m)` (`m = 0` : `p | d_j` only, `m = 1` :
`p | d'_j` only, `m = 2` : both), the local factor is
`1 + Σ_j (−x_jp z_jp − y_jp z_jp + x_jp y_jp z_jp)` — exactly the factor
`K_p` of Polymath8a (39) once the ξ-dependent divisor weights are plugged in.
-/

section CoordFactor

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

/-- Local weight of one active coordinate `j` at prime `p` in mode `m`:
`m = 0` (`p | d_j` only), `m = 1` (`p | d'_j` only), `m = 2` (`p | both`). -/
noncomputable def modeWeight (xjp yjp zjp : R) (m : Fin 3) : R :=
  if m = 0 then -(xjp * zjp) else if m = 1 then -(yjp * zjp) else xjp * yjp * zjp

/-- Per-prime weight of a configuration value `s : Option (Fin k × Fin 3)`:
`none` contributes 1 (p divides no `[d_j,d'_j]`), `some (j, m)` the local
mode weight of coordinate `j`. -/
noncomputable def configWeight {k : ℕ} (x y z : Fin k → ι → R) (p : ι)
    (s : Option (Fin k × Fin 3)) : R :=
  match s with
  | none => 1
  | some (j, m) => modeWeight (x j p) (y j p) (z j p) m

/-- The per-prime local factor of the pairwise-coprime k-coordinate sum:
`1 + Σ_j (−x_jp z_jp − y_jp z_jp + x_jp y_jp z_jp)`. -/
noncomputable def coordLocal {k : ℕ} (x y z : Fin k → ι → R) (p : ι) : R :=
  1 + ∑ j : Fin k, (-(x j p * z j p) + -(y j p * z j p) + x j p * y j p * z j p)

/-- The sum over the mode `m ∈ {A-only, B-only, both}` of the local weights. -/
lemma modeSum_eq (xjp yjp zjp : R) :
    (∑ m : Fin 3, modeWeight xjp yjp zjp m) =
      -(xjp * zjp) + -(yjp * zjp) + xjp * yjp * zjp := by
  rw [Fin.sum_univ_three]
  simp [modeWeight]

/-- Sum over all per-prime statuses equals the local factor. -/
theorem configLocalSum {k : ℕ} (x y z : Fin k → ι → R) (p : ι) :
    (∑ s : Option (Fin k × Fin 3), configWeight x y z p s) = coordLocal x y z p := by
  classical
  unfold coordLocal
  calc
    (∑ s : Option (Fin k × Fin 3), configWeight x y z p s)
        = configWeight x y z p none +
            (∑ s : Fin k × Fin 3, configWeight x y z p (some s)) := by
            rw [Fintype.sum_option]
    _ = 1 + ∑ j : Fin k, ∑ m : Fin 3, modeWeight (x j p) (y j p) (z j p) m := by
            simp [configWeight, Fintype.sum_prod_type]
    _ = 1 + ∑ j : Fin k,
          (-(x j p * z j p) + -(y j p * z j p) + x j p * y j p * z j p) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact modeSum_eq (x j p) (y j p) (z j p)

theorem coordFactor (S : Finset ι) {k : ℕ} (x y z : Fin k → ι → R) :
    (∑ σ : ({p // p ∈ S} → Option (Fin k × Fin 3)),
        ∏ p : {p // p ∈ S}, configWeight x y z p.1 (σ p)) =
      ∏ p ∈ S, coordLocal x y z p := by
  classical
  calc
    (∑ σ : ({p // p ∈ S} → Option (Fin k × Fin 3)),
        ∏ p : {p // p ∈ S}, configWeight x y z p.1 (σ p))
        = ∏ p : {p // p ∈ S}, ∑ s : Option (Fin k × Fin 3), configWeight x y z p.1 s := by
            exact (Fintype.prod_sum (ι := {p // p ∈ S})
              (κ := fun _ : {p // p ∈ S} => Option (Fin k × Fin 3))
              (f := fun p s => configWeight x y z p.1 s)).symm
    _ = ∏ p ∈ S, coordLocal x y z p := by
          calc
            (∏ p : {p // p ∈ S}, ∑ s : Option (Fin k × Fin 3), configWeight x y z p.1 s)
                = ∏ p ∈ S.attach, ∑ s : Option (Fin k × Fin 3), configWeight x y z p.1 s := by
                    rw [Finset.univ_eq_attach (s := S)]
            _ = ∏ p ∈ S, (∑ s : Option (Fin k × Fin 3), configWeight x y z p s) := by
                    exact Finset.prod_attach (s := S)
                      (f := fun p : ι => ∑ s : Option (Fin k × Fin 3), configWeight x y z p s)
            _ = ∏ p ∈ S, coordLocal x y z p := by
                    refine Finset.prod_congr rfl ?_
                    intro p hp
                    exact configLocalSum x y z p
end CoordFactor

/-! ## Concrete-instance sanity tests

The theorems are abstract over the ring `R` and prime type `ι`; these examples
verify the statements at small concrete instances (kernel `decide`), guarding
against sign/encoding slips in the local factors.  Per prime the local factor
with `x ≡ 5, y ≡ 7, z ≡ 11` is `1 - 55 - 77 + 385 = 254`, so for two primes
both sides are `254² = 64516` (one coordinate) and `(1 + 2·253)² = 507²`
(two coordinates, pairwise-coprime / at most one active coordinate per prime).
-/

open scoped BigOperators

example :
    (∑ A ∈ ({2, 3} : Finset ℕ).powerset, ∑ B ∈ ({2, 3} : Finset ℕ).powerset,
      pairTerm (fun _ : ℕ => (5 : ℤ)) (fun _ => (7 : ℤ)) (fun _ => (11 : ℤ)) A B) = 64516 := by
  decide

example :
    (∑ A ∈ ({2, 3} : Finset ℕ).powerset, ∑ B ∈ ({2, 3} : Finset ℕ).powerset,
      pairTerm (fun _ : ℕ => (5 : ℤ)) (fun _ => (7 : ℤ)) (fun _ => (11 : ℤ)) A B) =
      ∏ p ∈ ({2, 3} : Finset ℕ), pairLocal (fun _ : ℕ => (5 : ℤ)) (fun _ => (7 : ℤ))
        (fun _ => (11 : ℤ)) p := by
  exact pairFactor ({2, 3} : Finset ℕ) (fun _ : ℕ => (5 : ℤ)) (fun _ => (7 : ℤ))
    (fun _ => (11 : ℤ))

example :
    (∏ p ∈ ({2, 3} : Finset ℕ),
      coordLocal (fun _ : Fin 2 => fun _ : ℕ => (5 : ℤ))
        (fun _ => fun _ => (7 : ℤ)) (fun _ => fun _ => (11 : ℤ)) p) = 257049 := by
  decide

example :
    (∑ σ : ({p // p ∈ ({2, 3} : Finset ℕ)} → Option (Fin 2 × Fin 3)),
      ∏ p : {p // p ∈ ({2, 3} : Finset ℕ)},
        configWeight (fun _ : Fin 2 => fun _ : ℕ => (5 : ℤ))
          (fun _ => fun _ => (7 : ℤ)) (fun _ => fun _ => (11 : ℤ)) p.1 (σ p)) =
      ∏ p ∈ ({2, 3} : Finset ℕ),
        coordLocal (fun _ : Fin 2 => fun _ : ℕ => (5 : ℤ))
          (fun _ => fun _ => (7 : ℤ)) (fun _ => fun _ => (11 : ℤ)) p := by
  exact coordFactor ({2, 3} : Finset ℕ) (k := 2)
    (fun _ : Fin 2 => fun _ : ℕ => (5 : ℤ))
    (fun _ => fun _ => (7 : ℤ)) (fun _ => fun _ => (11 : ℤ))

end Commons.NumberTheory.MaynardSieve
