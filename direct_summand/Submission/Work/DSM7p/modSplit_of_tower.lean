import Mathlib
import Submission.Work.DSM7p.Basic

set_option linter.style.haveILetI false

namespace Work.DSM7p

universe a

open CategoryTheory
open scoped TensorProduct

/-- `iterTr` carries the `m`-th power of `p` in `D (n+c)` to the `m`-th power of `p` in `D n`,
hence the ideal `(p ^ m)` of `D (n+c)` into the ideal `(p ^ m)` of `D n`. -/
lemma iterTr_mem_span_pow {B : Type a} [CommRing B] {p : ℕ} {D : ℕ → Type a}
    [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)] (tr : ∀ n, D (n + 1) →ₐ[B] D n)
    (n c m : ℕ) {x : D (n + c)} (hx : x ∈ Ideal.span {(p : D (n + c)) ^ m}) :
    (DSMap.Mix.iterTr tr n c) x ∈ Ideal.span {(p : D n) ^ m} := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

/-- The elementary ring identity behind the transport: if `B i - G * C i ∈ I` for all `i ∈ s` and
`(∑ i, A i * C i) - W ∈ I`, then `(∑ i, A i * B i) - G * W ∈ I`. -/
lemma sum_mul_sub_mem {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*} (s : Finset ι)
    (A B C : ι → R) (G W : R)
    (h1 : ∀ i ∈ s, B i - G * C i ∈ I)
    (h2 : (∑ i ∈ s, A i * C i) - W ∈ I) :
    (∑ i ∈ s, A i * B i) - G * W ∈ I := by
  have key : (∑ i ∈ s, A i * B i) - G * W
      = (∑ i ∈ s, A i * (B i - G * C i)) + G * ((∑ i ∈ s, A i * C i) - W) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [show (∑ i ∈ s, A i * (G * C i)) = ∑ i ∈ s, G * (A i * C i) from
      Finset.sum_congr rfl (fun i hi => by ring)]
    ring
  rw [key]
  refine add_mem (Submodule.sum_mem _ fun i hi => ?_) (Ideal.mul_mem_left _ _ h2)
  exact Ideal.mul_mem_left _ _ (h1 i hi)

/-- **The RET tower gives almost-values over `B`.**  `P` is a bounded-above complex of finite free `A`-modules with coaugmentation `ε : A → P⁰`; `B` is an `A`-algebra; `Q : PerfectoidData p B`; `gr` is a system of compatible `p`-power roots of `g : A`; `D : ℕ → Type` is a tower of `B`-algebras with `tr : D (n+1) →ₐ[B] D n`, each `D n` carrying `PerfectoidData p (D n)` with the same `ϖ` as `Q` (`hQD`); `hq : IsQRETp p B Q.ϖ gr D tr` is the frozen pro-uniform quantitative Riemann extension predicate (kernel clause: for all `m k` there is `c` with `K_{n+c} = ker(B/p^m → D (n+c)/p^m)` killed by `ϖ k * gr k` for all `n`; cokernel clause: `ϖ k * gr k * iterTr tr n c (D (n+c)) ⊆ im(B) + p^m`); and `hsplit` says `ε` admits splittings over every `D n` modulo every `p^m` with value `(QD n).ϖ k`.

Conclusion: over `B` itself (modulo `p ^ m`) the value `(Q.ϖ k)^3 * (gr k)^2` is achieved.  Proof: with `c := c(m,k)` from `IsQRETp`, take the splitting `X : P⁰ → D (2c)/p^m` with value `ϖ k`, lift the finitely many values of `X` on a basis of `P⁰` to `D (2c)`, apply the cokernel clause at level `c` to get `β : P⁰ → B/p^m` with `ρ_c (β z) = ϖ k * gr k * iterTr (X z)` for all `z`, multiply by `ϖ k * gr k`, and use the (uniform in `n`) kernel clause at level `0` to see that the resulting functional kills `d⁻¹`.  The statement is deliberately weaker than the natural `Q.ϖ k * gr k` (the transport produces one extra root factor); the exponent pair `(3,2)` is exactly what the final Krull argument consumes. -/
theorem modSplit_of_tower {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (hP : DSMap.Mix.IsBddFinFree P)
    (p : ℕ) [Fact p.Prime] (B : Type a) [CommRing B] [Algebra A B] (Q : DSMap.PerfectoidData p B)
    (g : A) (gr : ℕ → B) (hgr0 : gr 0 = algebraMap A B g)
    (D : ℕ → Type a) [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)]
    (QD : ∀ n, DSMap.PerfectoidData p (D n)) (tr : ∀ n, D (n + 1) →ₐ[B] D n)
    (hQD : ∀ n k, (QD n).ϖ k = algebraMap B (D n) (Q.ϖ k))
    (hq : DSMap.Mix2.IsQRETp p B Q.ϖ gr D tr)
    (hsplit : ∀ n m k, DSMap.Mix.ModSplit P ε
      ((algebraMap B (D n)).comp (algebraMap A B)) (Ideal.span {(p : D n) ^ m}) ((QD n).ϖ k))
    (m k : ℕ) :
    DSMap.Mix.ModSplit P ε (algebraMap A B) (Ideal.span {(p : B) ^ m})
      ((Q.ϖ k) ^ 3 * (gr k) ^ 2) := by
  classical
  by_cases hA : Nontrivial A
  · haveI : Nontrivial A := hA
    haveI : Module.Free A (P.X 0) := (hP.1 0).1
    haveI : Module.Finite A (P.X 0) := (hP.1 0).2
    haveI : Module.Free A (P.X (-1)) := (hP.1 (-1)).1
    haveI : Module.Finite A (P.X (-1)) := (hP.1 (-1)).2
    obtain ⟨c, hK, hC⟩ := hq m k
    let b0 : Module.Basis (Fin (Module.finrank A (P.X 0))) A (P.X 0) := Module.finBasis A (P.X 0)
    let b1 : Module.Basis (Fin (Module.finrank A (P.X (-1)))) A (P.X (-1)) :=
      Module.finBasis A (P.X (-1))
    -- the splitting over `D (c + c)`, in matrix form
    have hs2 := hsplit (c + c) m k
    rw [Work.DSAM2.modSplit_iff_mulVec P ε ((algebraMap B (D (c + c))).comp (algebraMap A B))
        (Ideal.span {(p : D (c + c)) ^ m}) ((QD (c + c)).ϖ k) b0 b1] at hs2
    obtain ⟨q2, hq2⟩ := hs2
    -- lifts of the coordinate values to `D (c + c)`
    have hlift : ∀ i, ∃ Y : D (c + c),
        Ideal.Quotient.mk (Ideal.span {(p : D (c + c)) ^ m}) Y = q2 i :=
      fun i => Ideal.Quotient.mk_surjective (q2 i)
    choose Y hY using hlift
    -- the cokernel clause at level `c`, giving the corrections in `B`
    have hcorr : ∀ i, ∃ b : B, (algebraMap B (D c)) (Q.ϖ k * gr k) * (DSMap.Mix.iterTr tr c c) (Y i)
        - (algebraMap B (D c)) b ∈ Ideal.span {(p : D c) ^ m} := fun i => hC c (Y i)
    choose bb hbb using hcorr
    let Z : Option (Fin (Module.finrank A (P.X (-1)))) → B := fun kk =>
      ∑ i, algebraMap A B (Work.DSAM2.systemMatrix P ε b0 b1 kk i) * bb i
    have hbbρ : ∀ i, (algebraMap B (D c)) (bb i)
        - (algebraMap B (D c)) (Q.ϖ k * gr k) * (DSMap.Mix.iterTr tr c c) (Y i)
        ∈ Ideal.span {(p : D c) ^ m} := by
      intro i
      have h' : -((algebraMap B (D c)) (Q.ϖ k * gr k) * (DSMap.Mix.iterTr tr c c) (Y i)
          - (algebraMap B (D c)) (bb i)) ∈ Ideal.span {(p : D c) ^ m} := neg_mem (hbb i)
      rwa [neg_sub] at h'
    -- the system of equations over `D (c + c)`, promoted from the quotient to an ideal membership
    have hmem : ∀ kk : Option (Fin (Module.finrank A (P.X (-1)))),
        (∑ i, (algebraMap B (D (c + c))) (algebraMap A B
            (Work.DSAM2.systemMatrix P ε b0 b1 kk i)) * Y i)
          - (Work.DSAM2.systemRHS ((QD (c + c)).ϖ k) kk)
          ∈ Ideal.span {(p : D (c + c)) ^ m} := by
      intro kk
      rw [← Ideal.Quotient.eq]
      have hrow := congrFun hq2 kk
      simp only [Matrix.map_apply, Matrix.mulVec, dotProduct] at hrow
      rw [map_sum]
      rw [show (∑ i, Ideal.Quotient.mk (Ideal.span {(p : D (c + c)) ^ m})
              ((algebraMap B (D (c + c))) (algebraMap A B
                (Work.DSAM2.systemMatrix P ε b0 b1 kk i)) * Y i))
            = ∑ i, Ideal.Quotient.mk (Ideal.span {(p : D (c + c)) ^ m})
              ((algebraMap B (D (c + c))) (algebraMap A B
                (Work.DSAM2.systemMatrix P ε b0 b1 kk i))) * q2 i
          from Finset.sum_congr rfl (fun i _ => by rw [map_mul, hY i])]
      exact hrow
    -- the same system at level `c`, obtained by applying `iterTr tr c c`
    have hZc : ∀ kk, (algebraMap B (D c)) (Z kk)
        - (algebraMap B (D c)) (Q.ϖ k * gr k) * (DSMap.Mix.iterTr tr c c)
            (Work.DSAM2.systemRHS ((QD (c + c)).ϖ k) kk)
        ∈ Ideal.span {(p : D c) ^ m} := by
      intro kk
      have h1 : (∑ i, (algebraMap B (D c)) (algebraMap A B
              (Work.DSAM2.systemMatrix P ε b0 b1 kk i))
            * (DSMap.Mix.iterTr tr c c) (Y i))
          - (DSMap.Mix.iterTr tr c c) (Work.DSAM2.systemRHS ((QD (c + c)).ϖ k) kk)
          ∈ Ideal.span {(p : D c) ^ m} := by
        have h := iterTr_mem_span_pow tr c c m (hmem kk)
        rw [map_sub, map_sum] at h
        rw [show (∑ i, (DSMap.Mix.iterTr tr c c)
              ((algebraMap B (D (c + c))) (algebraMap A B
                (Work.DSAM2.systemMatrix P ε b0 b1 kk i)) * Y i))
            = ∑ i, (algebraMap B (D c)) (algebraMap A B
                (Work.DSAM2.systemMatrix P ε b0 b1 kk i))
              * (DSMap.Mix.iterTr tr c c) (Y i)
          from Finset.sum_congr rfl (fun i _ => by rw [map_mul, AlgHom.commutes])] at h
        exact h
      have h2 := sum_mul_sub_mem (Ideal.span {(p : D c) ^ m}) Finset.univ
        (fun i => (algebraMap B (D c)) (algebraMap A B
          (Work.DSAM2.systemMatrix P ε b0 b1 kk i)))
        (fun i => (algebraMap B (D c)) (bb i))
        (fun i => (DSMap.Mix.iterTr tr c c) (Y i))
        ((algebraMap B (D c)) (Q.ϖ k * gr k))
        ((DSMap.Mix.iterTr tr c c) (Work.DSAM2.systemRHS ((QD (c + c)).ϖ k) kk))
        (fun i _ => hbbρ i) h1
      have h2' : (∑ i, (algebraMap B (D c)) (algebraMap A B
            (Work.DSAM2.systemMatrix P ε b0 b1 kk i)) * (algebraMap B (D c)) (bb i))
          = (algebraMap B (D c)) (Z kk) := by
        dsimp only [Z]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul]
      rwa [h2'] at h2
    -- the kernel clause at level `0` (i.e. at level `c`) over the `none`-row
    have hkerN : (Q.ϖ k * gr k) * Z none - (Q.ϖ k) ^ 3 * (gr k) ^ 2
        ∈ Ideal.span {(p : B) ^ m} := by
      have hZ0 := hZc none
      simp only [Work.DSAM2.systemRHS] at hZ0
      rw [hQD (c + c) k, AlgHom.commutes] at hZ0
      have hZ1 : (algebraMap B (D c)) (Z none - (Q.ϖ k) ^ 2 * gr k)
          ∈ Ideal.span {(p : D c) ^ m} := by
        rw [map_sub, map_mul, map_pow]
        convert hZ0 using 1
        rw [map_mul]
        ring
      have hthis := hK 0 (Z none - (Q.ϖ k) ^ 2 * gr k)
      rw [Nat.zero_add] at hthis
      have h := hthis hZ1
      rw [mul_sub] at h
      convert h using 1
      ring
    -- the kernel clause at level `0` over the differential rows
    have hkerJ : ∀ j, (Q.ϖ k * gr k) * Z (some j) ∈ Ideal.span {(p : B) ^ m} := by
      intro j
      have hZj := hZc (some j)
      simp only [Work.DSAM2.systemRHS, map_zero, mul_zero, sub_zero] at hZj
      have hthis := hK 0 (Z (some j))
      rw [Nat.zero_add] at hthis
      exact hthis hZj
    -- assemble the splitting over `B`
    let q : Fin (Module.finrank A (P.X 0)) → B ⧸ Ideal.span {(p : B) ^ m} :=
      fun i => Ideal.Quotient.mk (Ideal.span {(p : B) ^ m}) ((Q.ϖ k * gr k) * bb i)
    rw [Work.DSAM2.modSplit_iff_mulVec P ε (algebraMap A B) (Ideal.span {(p : B) ^ m})
        ((Q.ϖ k) ^ 3 * (gr k) ^ 2) b0 b1]
    refine ⟨q, ?_⟩
    funext kk
    have hL : (∑ i, Ideal.Quotient.mk (Ideal.span {(p : B) ^ m})
            (algebraMap A B (Work.DSAM2.systemMatrix P ε b0 b1 kk i)) * q i)
        = Ideal.Quotient.mk (Ideal.span {(p : B) ^ m}) ((Q.ϖ k * gr k) * Z kk) := by
      have e1 : (∑ i, Ideal.Quotient.mk (Ideal.span {(p : B) ^ m})
            (algebraMap A B (Work.DSAM2.systemMatrix P ε b0 b1 kk i)) * q i)
          = Ideal.Quotient.mk (Ideal.span {(p : B) ^ m})
              (∑ i, algebraMap A B (Work.DSAM2.systemMatrix P ε b0 b1 kk i)
                * ((Q.ϖ k * gr k) * bb i)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [q]
        simp only [map_mul]
      rw [e1]
      congr 1
      dsimp only [Z]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    cases kk with
    | none =>
      simp only [Matrix.map_apply, Matrix.mulVec, dotProduct, Work.DSAM2.systemRHS]
      rw [hL, Ideal.Quotient.eq]
      exact hkerN
    | some j =>
      simp only [Matrix.map_apply, Matrix.mulVec, dotProduct, Work.DSAM2.systemRHS]
      rw [hL, Ideal.Quotient.eq]
      simpa using hkerJ j
  · exact Work.DSAM2.modSplit_of_subsingleton P ε (algebraMap A B) (Ideal.span {(p : B) ^ m})
      ((Q.ϖ k) ^ 3 * (gr k) ^ 2) (not_nontrivial_iff_subsingleton.mp hA)

end Work.DSM7p
