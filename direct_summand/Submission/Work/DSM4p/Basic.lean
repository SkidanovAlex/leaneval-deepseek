import Submission.Work.DSMap.Mix2

/-!
# DSM4p — vocabulary and API for the Riemann extension tower (`area_M4p`)

This is the entry module of the subproject `Submission/Work/DSM4p/`, which owns the frozen
node

  `DSMap.Mix2.area_M4p`

of the read-only file `Submission/Work/DSMap/Mix2.lean` (the `M4p` node of
`sources/dsmap/direct_summand_mix2.md`, i.e. Bhatt, *The direct summand conjecture and its
derived variant*, arXiv:1608.08882, §3: Theorem 3.1 together with Remark 3.2).

## The node

For a `p`-torsion-free `p`-adically complete integral perfectoid ring `B`
(`DSMap.PerfectoidData p B`, `p` prime) and *any* compatible system `gr` of `p`-power roots
(`gr (k+1)^p = gr k`, so `gr k = (gr 0)^{1/p^k}`) of an element `g = gr 0 ∈ B`, there must be

* a tower of rings `D 0 ← D 1 ← D 2 ← ⋯` (`tr n : D (n+1) →ₐ[B] D n`),
* each `D n` again perfectoid (`QD n : PerfectoidData p (D n)`) with the *same*
  pseudo-uniformiser (`(QD n).ϖ k = algebraMap B (D n) (Q.ϖ k)`),
* in which `g` divides `p ^ n` (`∃ y, algebraMap B (D n) (gr 0) * y = (p : D n) ^ n`),

such that the induced map of pro-systems `{B/p^m} → {D n/p^m}` is a *uniform* almost
pro-isomorphism with respect to `(ϖ · g)^{1/p^∞}` — this is `DSMap.Mix2.IsQRETp`, the pro
form with a single constant `c` shared by the kernel and the cokernel clause:

`∀ m k, ∃ c, (∀ n x, x ↦ 0 in D (n+c) mod p^m → ϖ_k g_k x ∈ p^m B) ∧`
`          (∀ n y, ∃ x, ϖ_k g_k · (iterTr tr n c y) ≡ x mod p^m in D n)`.

The mathematical content (Scholze's Hebbarkeitssatz, in the quantitative form of Bhatt's
Theorem 3.1) is the Riemann extension theorem for perfectoid spaces; the point of the pro
form is Remark 3.2: the kernel clause need *not* hold at a fixed level `n`, only after moving
sufficiently far up the tower, and this weakening is what makes the statement true without a
nonzerodivisor hypothesis on `g`.

## Contents of this file

* `Work.DSM4p.IsRootSystem` — compatible systems of `p`-power roots and their iterates
  (`IsRootSystem.pow_pow`: `gr (k+n)^(p^n) = gr k`);
* `Work.DSM4p.iterTr` API — the iterated transition maps of the tower in the element-level
  form used by consumers (`iterTr_zero`, `iterTr_one`, `iterTr_succ_apply`,
  `iterTr_zero_apply`, `iterTr_one_apply`, `iterTr_algebraMap`);
* `Work.DSM4p.IsQRETAt` — the QRET condition at a fixed level `(m, k)`; `IsQRETp` is
  *definitionally* `∀ m k, IsQRETAt …` (`isQRETp_iff_isQRETAt`);
* `Work.DSM4p.isQRETp_self` — the stationary tower `D n = B` satisfies the QRET condition
  (with `c = 0`): the two clauses are satisfiable, and this is the sanity check on the
  formalisation of the conditions;
* `Work.DSM4p.isQRETp_of_retractions` — if every level of the tower retracts `B`-linearly
  onto `B` and the transitions factor through the retractions, then the QRET condition holds
  (the "lossless tower" case; it isolates the shape of both clauses);
* `Work.DSM4p.RETTower` — the bundled data of the node, with `Work.DSM4p.area_M4p_iff`
  restating `area_M4p` as the existence of such a bundle.

The construction of the tower itself (the explicit chart algebras `B[u_n^{1/p^∞}]` with
`(u_n g)^{1/p^k} = ϖ_k^n`) lives in `Submission/Work/DSM4p/Chart.lean`; the quantitative
estimates behind the QRET clauses live in `Submission/Work/DSM4p/chartMono_estimate.lean`,
`Submission/Work/DSM4p/chartTower_cokernel.lean` and `Submission/Work/DSM4p/chartCokernel.lean`,
and the completed levels of the tower in `Submission/Work/DSM4p/Completion.lean`.
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

/-! ## 1. Compatible systems of `p`-power roots -/

/-- `r` is a compatible system of `p`-power roots: `r (k+1) ^ p = r k`.  (The same notion as
`Work.DSM2p.IsRootSystem`; kept here so that the `DSM4p` area is self-contained.) -/
def IsRootSystem {B : Type a} [CommRing B] (p : ℕ) (r : ℕ → B) : Prop :=
  ∀ k : ℕ, r (k + 1) ^ p = r k

/-- `r (k+n)` is a `p^n`-th root of `r k`. -/
theorem IsRootSystem.pow_pow {B : Type a} [CommRing B] {p : ℕ} {r : ℕ → B}
    (h : IsRootSystem p r) (k n : ℕ) : r (k + n) ^ p ^ n = r k := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc r (k + (n + 1)) ^ p ^ (n + 1)
        = (r (k + n + 1) ^ p) ^ p ^ n := by rw [Nat.add_succ, pow_succ', pow_mul]
      _ = r (k + n) ^ p ^ n := by rw [h (k + n)]
      _ = r k := ih

/-- The defining property read at `0`: `r n` is a `p^n`-th root of `r 0`. -/
theorem IsRootSystem.pow_pow_zero {B : Type a} [CommRing B] {p : ℕ} {r : ℕ → B}
    (h : IsRootSystem p r) (n : ℕ) : r n ^ p ^ n = r 0 := by
  simpa using h.pow_pow 0 n

/-! ## 2. The iterated transition maps `iterTr`

`DSMap.Mix.iterTr tr n c : D (n+c) →ₐ[B] D n` is the `c`-fold composite of the transitions.
We record the element-level API (the `AlgHom` equalities are the definitional unfoldings). -/

section IterTr

variable {B : Type a} [CommRing B] {D : ℕ → Type a} [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)]
  (tr : ∀ n, D (n + 1) →ₐ[B] D n)

/-- `iterTr` in degree `0` is the identity. -/
theorem iterTr_zero (n : ℕ) : iterTr tr n 0 = AlgHom.id B (D n) := rfl

/-- The defining recursion of `iterTr`. -/
theorem iterTr_succ (n c : ℕ) :
    iterTr tr n (c + 1) = (iterTr tr n c).comp (tr (n + c)) := rfl

/-- `iterTr` in degree `1` is the transition itself. -/
theorem iterTr_one (n : ℕ) : iterTr tr n 1 = tr n := by
  show iterTr tr n (0 + 1) = tr n
  rw [iterTr_succ, iterTr_zero]
  exact AlgHom.id_comp (tr n)

/-- Element form of the defining recursion. -/
theorem iterTr_succ_apply (n c : ℕ) (y : D (n + (c + 1))) :
    iterTr tr n (c + 1) y = iterTr tr n c (tr (n + c) y) := rfl

/-- Element form of `iterTr_zero`. -/
@[simp] theorem iterTr_zero_apply (n : ℕ) (y : D (n + 0)) : iterTr tr n 0 y = y := rfl

/-- Element form of `iterTr_one`. -/
theorem iterTr_one_apply (n : ℕ) (y : D (n + 1)) : iterTr tr n 1 y = tr n y := by
  rw [iterTr_one]

/-- `iterTr` fixes the image of `B`: the tower is a tower of `B`-algebras. -/
theorem iterTr_algebraMap (n c : ℕ) (b : B) :
    iterTr tr n c (algebraMap B (D (n + c)) b) = algebraMap B (D n) b :=
  AlgHom.commutes (iterTr tr n c) b

end IterTr

/-! ## 3. The QRET condition, level by level -/

/-- `IsQRETp` at a fixed pair `(m, k)`: the two quantitative clauses of Bhatt's Theorem 3.1
with a single constant `c` (the "uniform" pro form).  `DSMap.Mix2.IsQRETp` is, by definition,
`∀ m k, IsQRETAt … m k`. -/
def IsQRETAt (p : ℕ) (B : Type a) [CommRing B] (ϖ gr : ℕ → B) (D : ℕ → Type a)
    [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)] (tr : ∀ n, D (n + 1) →ₐ[B] D n)
    (m k : ℕ) : Prop :=
  ∃ c : ℕ,
    (∀ n (x : B), algebraMap B (D (n + c)) x ∈ Ideal.span {((p : D (n + c))) ^ m} →
        ϖ k * gr k * x ∈ Ideal.span {(p : B) ^ m}) ∧
    (∀ n (y : D (n + c)), ∃ x : B,
        algebraMap B (D n) (ϖ k * gr k) * iterTr tr n c y - algebraMap B (D n) x ∈
          Ideal.span {(p : D n) ^ m})

/-- The frozen `IsQRETp` is exactly the conjunction of its levels. -/
theorem isQRETp_iff_isQRETAt (p : ℕ) (B : Type a) [CommRing B] (ϖ gr : ℕ → B)
    (D : ℕ → Type a) [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)]
    (tr : ∀ n, D (n + 1) →ₐ[B] D n) :
    IsQRETp p B ϖ gr D tr ↔ ∀ m k, IsQRETAt p B ϖ gr D tr m k := Iff.rfl

/-- The kernel clause and the cokernel clause of `IsQRETp`, extracted at a fixed level. -/
theorem IsQRETp.apply (p : ℕ) (B : Type a) [CommRing B] (ϖ gr : ℕ → B) (D : ℕ → Type a)
    [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)] (tr : ∀ n, D (n + 1) →ₐ[B] D n)
    (h : IsQRETp p B ϖ gr D tr) (m k : ℕ) : IsQRETAt p B ϖ gr D tr m k := h m k

/-! ### The stationary tower satisfies the condition

For `D n = B` (the identity tower) both clauses hold with `c = 0`: the kernel clause is
`p^m · B` being an ideal, and the cokernel clause is solved by `x = ϖ_k g_k · y`.  This shows
that the two clauses of `IsQRETp` are consistent; the content of the node is that they hold
*together with* `g ∣ p^n` and perfectoidness of every level. -/

/-- The stationary tower `D n = B` satisfies the QRET condition. -/
theorem isQRETp_self (p : ℕ) (B : Type a) [CommRing B] (ϖ gr : ℕ → B) :
    IsQRETp p B ϖ gr (fun _ => B) (fun _ => AlgHom.id B B) := by
  intro m k
  refine ⟨0, ?_, ?_⟩
  · intro n x hx
    exact Ideal.mul_mem_left _ _ hx
  · intro n y
    exact ⟨ϖ k * gr k * y, by simp⟩

/-! ### The lossless (retractive) tower satisfies the condition

If every level of the tower admits a `B`-algebra retraction onto `B` through which the
transitions factor, then `IsQRETp` holds with `c = 1`.  This exhibits the shape of the
condition: the *kernel* clause is read off from the retraction (an element of `B` that dies
mod `p^m` in `D (n+1)` was already `0` mod `p^m` in `B`), and the *cokernel* clause is
immediate because the transition has image inside `B`.  In this case the divisibility clause
`∃ y, g * y = p^n` forces `g ∣ p^n` already in `B`, so this does not prove the node; it
isolates what the genuine construction has to supply instead. -/

/-- A tower whose transitions all land in the image of `B` satisfies `IsQRETp`. -/
theorem isQRETp_of_retractions (p : ℕ) (B : Type a) [CommRing B] (ϖ gr : ℕ → B)
    (D : ℕ → Type a) [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)]
    (tr : ∀ n, D (n + 1) →ₐ[B] D n) (ρ : ∀ n, D n →+* B)
    (hρ : ∀ n (b : B), ρ n (algebraMap B (D n) b) = b)
    (htr : ∀ n (y : D (n + 1)), tr n y = algebraMap B (D n) (ρ (n + 1) y)) :
    IsQRETp p B ϖ gr D tr := by
  intro m k
  refine ⟨1, ?_, ?_⟩
  · intro n x hx
    have hx' : x ∈ Ideal.span {(p : B) ^ m} := by
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hx
      have h := congrArg (ρ (n + 1)) hz
      rw [map_mul, map_pow, map_natCast, hρ (n + 1) x] at h
      rw [← h]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton'.mpr ⟨1, by simp⟩)
    exact Ideal.mul_mem_left _ _ hx'
  · intro n y
    refine ⟨ϖ k * gr k * ρ (n + 1) y, ?_⟩
    have h : iterTr tr n 1 y = algebraMap B (D n) (ρ (n + 1) y) := by
      rw [iterTr_one]
      exact htr n y
    rw [h]
    simp

/-! ## 4. The bundled node -/

/-- The data and the three conclusions of `area_M4p`: a perfectoid tower over `B` with the
same pseudo-uniformiser, in which `g = gr 0` divides `p ^ n`, and which satisfies the
pro-uniform almost-pro-isomorphism condition `IsQRETp`. -/
structure RETTower (p : ℕ) (B : Type a) [CommRing B] (Q : PerfectoidData p B) (gr : ℕ → B) where
  /-- the levels of the tower -/
  D : ℕ → Type a
  /-- the ring structure on each level -/
  [instCommRing : ∀ n, CommRing (D n)]
  /-- the `B`-algebra structure on each level -/
  [instAlgebra : ∀ n, Algebra B (D n)]
  /-- every level is perfectoid -/
  QD : ∀ n, PerfectoidData p (D n)
  /-- the transition maps -/
  tr : ∀ n, D (n + 1) →ₐ[B] D n
  /-- the pseudo-uniformisers agree -/
  varpi_eq : ∀ n k, (QD n).ϖ k = algebraMap B (D n) (Q.ϖ k)
  /-- `g = gr 0` divides `p ^ n` in the `n`-th level -/
  dvd : ∀ n, ∃ y : D n, algebraMap B (D n) (gr 0) * y = (p : D n) ^ n
  /-- the pro-uniform almost-pro-isomorphism condition -/
  qret : IsQRETp p B Q.ϖ gr D tr

/-- The *conclusion* of the node `area_M4p`, written out as a proposition (so that it can be
used on either side of an `↔`, unlike the proof term `DSMap.Mix2.area_M4p p B Q gr hgr`). -/
def AreaM4p (p : ℕ) (B : Type a) [CommRing B] (Q : PerfectoidData p B) (gr : ℕ → B) : Prop :=
  ∃ (D : ℕ → Type a) (_ : ∀ n, CommRing (D n)) (_ : ∀ n, Algebra B (D n))
    (QD : ∀ n, PerfectoidData p (D n)) (tr : ∀ n, D (n + 1) →ₐ[B] D n),
    (∀ n k, (QD n).ϖ k = algebraMap B (D n) (Q.ϖ k)) ∧
    (∀ n, ∃ y : D n, algebraMap B (D n) (gr 0) * y = (p : D n) ^ n) ∧
    IsQRETp p B Q.ϖ gr D tr

/-- `AreaM4p` is exactly the existence of the bundled data. -/
theorem areaM4p_iff (p : ℕ) (B : Type a) [CommRing B] (Q : PerfectoidData p B)
    (gr : ℕ → B) : AreaM4p p B Q gr ↔ Nonempty (RETTower p B Q gr) := by
  constructor
  · rintro ⟨D, hC, hA, QD, tr, hv, hd, hq⟩
    letI := hC
    letI := hA
    exact ⟨{ D := D, QD := QD, tr := tr, varpi_eq := hv, dvd := hd, qret := hq }⟩
  · rintro ⟨T⟩
    exact ⟨T.D, T.instCommRing, T.instAlgebra, T.QD, T.tr, T.varpi_eq, T.dvd, T.qret⟩


end Work.DSM4p
