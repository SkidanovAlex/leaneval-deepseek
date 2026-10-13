import Submission.Work.DSM1p.Basic

/-!
# DSM1p — the multi-parameter root tower `A[x₁^{1/p^∞}, …, x_d^{1/p^∞}]`

This module generalises `Work.DSM1p.Basic` from one parameter to a regular system of parameters
`x : Fin d → A`, as required by the curric-46 design
(`sources/dsmap/direct_summand_gaps_1013.md`, §2.2, and the lead's message of 2026-10-13):

* `FamTower R p x n = R[Z] ⧸ (Z_i ^ p^n - x_i)` — the `n`-th stage; free of rank `p ^ (n * d)`
  over `R`, hence flat;
* `FamClosure R p x` — the filtered colimit `A_∞ = colim_n A_n`;
* `FamCompletion R p x` — its `p`-adic completion `A′` (the ring of Bhatt's construction).

The cocycle of the tower is `Z_i^{(n)} ↦ (Z_i^{(n+1)}) ^ p`, i.e. the `n`-th root of `x_i` is
the `p`-th power of the `(n+1)`-st, exactly as in the one-parameter case.
-/

namespace Work.DSM1p

universe u

open MvPolynomial

/-! ## The stages -/

/-- **The `n`-th stage** of the multi-parameter root tower: `R[Z] / (Z_i ^ p^n - x_i)`. -/
noncomputable abbrev FamTower (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (n : ℕ) : Type u :=
  MvPolynomial (Fin d) R ⧸
    Ideal.span (Set.range fun i => (MvPolynomial.X i) ^ (p ^ n) - MvPolynomial.C (x i))

/-- The class of the `i`-th variable in the `n`-th stage, i.e. the `p^n`-th root of `x i`. -/
noncomputable abbrev FamTower.root (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (n : ℕ) (i : Fin d) : FamTower R p x n :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- The defining relation of the stage: `(root i) ^ p^n = x i`. -/
theorem FamTower.root_pow (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (n : ℕ) (i : Fin d) :
    (FamTower.root R p x n i) ^ (p ^ n) = algebraMap R (FamTower R p x n) (x i) := by
  have h : (Ideal.Quotient.mk _ (MvPolynomial.X i ^ (p ^ n) - MvPolynomial.C (x i)) :
      FamTower R p x n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [map_sub, map_pow] at h
  rw [show algebraMap R (FamTower R p x n) (x i) =
      (Ideal.Quotient.mk _ (MvPolynomial.C (x i)) : FamTower R p x n) from rfl,
    ← sub_eq_zero]
  exact h

/-- **The transition map** of the tower: the `n`-th root of `x_i` is the `p`-th power of the
`(n+1)`-st. -/
noncomputable def FamTower.step (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (n : ℕ) : FamTower R p x n →+* FamTower R p x (n + 1) :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom (algebraMap R (FamTower R p x (n + 1)))
      (fun i => (FamTower.root R p x (n + 1) i) ^ p)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul]
    have h0 : MvPolynomial.eval₂Hom (algebraMap R (FamTower R p x (n + 1)))
        (fun i => (FamTower.root R p x (n + 1) i) ^ p)
        (MvPolynomial.X i ^ (p ^ n) - MvPolynomial.C (x i)) = 0 := by
      rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
      refine sub_eq_zero.mpr ?_
      rw [← pow_mul, show p * p ^ n = p ^ (n + 1) from (pow_succ' p n).symm, FamTower.root_pow]
    rw [h0, mul_zero])

/-- The transition map sends the `n`-th root to the `p`-th power of the `(n+1)`-st root. -/
theorem FamTower.step_root (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (n : ℕ) (i : Fin d) :
    FamTower.step R p x n (FamTower.root R p x n i) =
      (FamTower.root R p x (n + 1) i) ^ p := by
  simp only [FamTower.step, FamTower.root]
  rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']

/-- The iterated transition map `A_n → A_{n+k}`. -/
noncomputable def FamTower.stepIter (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (n : ℕ) : ∀ k, FamTower R p x n →+* FamTower R p x (n + k)
  | 0 => RingHom.id _
  | k + 1 => (FamTower.step R p x (n + k)).comp (FamTower.stepIter R p x n k)

/-- The transition maps in the form required by a filtered colimit. -/
noncomputable def FamTower.stepMap (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (m n : ℕ) (h : m ≤ n) : FamTower R p x m →+* FamTower R p x n :=
  (Nat.add_sub_cancel' h) ▸ FamTower.stepIter R p x m (n - m)

/-- **The root closure** `A_∞ = A[x₁^{1/p^∞}, …, x_d^{1/p^∞}]`: the filtered colimit of the
stage tower. -/
noncomputable abbrev FamClosure (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) :
    Type u :=
  Ring.DirectLimit (FamTower R p x) fun m n h => ⇑(FamTower.stepMap R p x m n h)

/-- The canonical map from the `n`-th stage into the closure. -/
noncomputable abbrev FamClosure.of (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (n : ℕ) : FamTower R p x n →+* FamClosure R p x :=
  Ring.DirectLimit.of (FamTower R p x) (fun m n h => ⇑(FamTower.stepMap R p x m n h)) n

/-- The structure map `R → A_∞` through the zeroth stage. -/
noncomputable abbrev FamClosure.algebraMap' (R : Type u) [CommRing R] (p : ℕ) {d : ℕ}
    (x : Fin d → R) : R →+* FamClosure R p x :=
  (FamClosure.of R p x 0).comp (algebraMap R (FamTower R p x 0))

/-- The `R`-algebra structure on the closure. -/
noncomputable instance FamClosure.instAlgebra (R : Type u) [CommRing R] (p : ℕ) {d : ℕ}
    (x : Fin d → R) : Algebra R (FamClosure R p x) :=
  (FamClosure.algebraMap' R p x).toAlgebra

/-- **The root tower data.**  `varpi n i` is the `p^n`-th root of `x i` that sits in the
`(n+1)`-st stage. -/
noncomputable def FamClosure.rootTower (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (n : ℕ) (i : Fin d) : FamClosure R p x :=
  FamClosure.of R p x (n + 1) (FamTower.root R p x (n + 1) i)

/-! ## The `p`-adic completion -/

/-- **The `p`-adic completion** `A′` of the closure, the ring of Bhatt's construction. -/
noncomputable abbrev FamCompletion (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) :
    Type u :=
  AdicCompletion (Ideal.span {(p : FamClosure R p x)}) (FamClosure R p x)

/-- The structure map `A_∞ → A′`. -/
noncomputable abbrev FamCompletion.of (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) :
    FamClosure R p x →+* FamCompletion R p x :=
  algebraMap (FamClosure R p x) (FamCompletion R p x)

/-- The structure map `R → A′`. -/
noncomputable abbrev FamCompletion.algebraMap' (R : Type u) [CommRing R] (p : ℕ) {d : ℕ}
    (x : Fin d → R) : R →+* FamCompletion R p x :=
  (FamCompletion.of R p x).comp (FamClosure.algebraMap' R p x)

/-- The `R`-algebra structure on the completion. -/
noncomputable instance FamCompletion.instAlgebra (R : Type u) [CommRing R] (p : ℕ) {d : ℕ}
    (x : Fin d → R) : Algebra R (FamCompletion R p x) :=
  (FamCompletion.algebraMap' R p x).toAlgebra

/-! ## The SER hypothesis, taken as an explicit input

The shared frozen node `DSMap.Gaps.area_SER` (the Cohen-free series lemma of the curric-46
design) is currently `sorry` in the read-only file `Submission/Work/DSMap/Gaps.lean`.  Until the
subproject `DSSER` delivers it, the two Cohen-free inputs of `frobSurj` and of the
pseudo-uniformizer `ϖ` are stated with the following *explicit hypothesis*, so that the
statements are sorry-free and become unconditional once `area_SER` is imported. -/

/-- **The SER hypothesis** (`DSMap.Gaps.area_SER`, verbatim): for a complete Noetherian local ring
`S` with perfect residue field (`hperf`), `p ∈ 𝔪_S` and `z` generating `𝔪_S`, and for every
`a : S` there are `b, h` in `S[Z]/(Z_i ^ p - z_i)` with `b ^ p = a + p * h`, and `h ∈ (Z)` when
`a ∈ 𝔪_S`. -/
def SERHyp (p : ℕ) : Prop :=
  ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S],
    IsAdicComplete (IsLocalRing.maximalIdeal S) S → (p : S) ∈ IsLocalRing.maximalIdeal S →
    (∀ y : S, ∃ μ : S, y - μ ^ p ∈ IsLocalRing.maximalIdeal S) →
    ∀ {e : ℕ} (z : Fin e → S), Ideal.span (Set.range z) = IsLocalRing.maximalIdeal S →
    ∀ a : S,
      ∃ b h : MvPolynomial (Fin e) S ⧸
          Ideal.span (Set.range fun i => (MvPolynomial.X i) ^ p - MvPolynomial.C (z i)),
        b ^ p = algebraMap S _ a + (p : S) • h ∧
        (a ∈ IsLocalRing.maximalIdeal S → h ∈ Ideal.span (Set.range fun i =>
          Ideal.Quotient.mk _ (MvPolynomial.X i)))

/-- **The NORM hypothesis** (`DSMap.Gaps.area_NORM`, subproject `DSNORM`, verbatim): a regular
local ring is integrally closed.  It is the second shared Cohen-free input of the curric-46 design
(`sources/dsmap/direct_summand_gaps_1013.md` §2.2 item 3); it is taken as an explicit hypothesis
here because the frozen node is currently `sorry` and its proof still depends on `sorryAx`. -/
def NORMHyp : Prop := ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S], IsIntegrallyClosed S

/-! ## Algebra structures on the reductions modulo `p` -/

/-- The `R ⧸ (p)`-algebra structure on the reduction of the closure modulo `p`. -/
noncomputable instance FamClosure.modPAlgebra (R : Type u) [CommRing R] (p : ℕ) {d : ℕ}
    (x : Fin d → R) : Algebra (R ⧸ Ideal.span {(p : R)})
      (FamClosure R p x ⧸ Ideal.span {(p : FamClosure R p x)}) :=
  Ideal.Quotient.algebraQuotientOfLEComap (by
    rw [Ideal.span_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Ideal.mem_comap.mpr (by
      rw [map_natCast]
      exact Ideal.subset_span (Set.mem_singleton _)))

/-- The `R ⧸ (p)`-algebra structure on the reduction of the completion modulo `p`. -/
noncomputable instance FamCompletion.modPAlgebra (R : Type u) [CommRing R] (p : ℕ) {d : ℕ}
    (x : Fin d → R) : Algebra (R ⧸ Ideal.span {(p : R)})
      (FamCompletion R p x ⧸ Ideal.span {(p : FamCompletion R p x)}) :=
  Ideal.Quotient.algebraQuotientOfLEComap (by
    rw [Ideal.span_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Ideal.mem_comap.mpr (by
      rw [map_natCast]
      exact Ideal.subset_span (Set.mem_singleton _)))

end Work.DSM1p
