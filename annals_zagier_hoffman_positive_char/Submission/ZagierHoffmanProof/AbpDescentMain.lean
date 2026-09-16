import Submission.ZagierHoffmanProof.AbpDescent
import Submission.ZagierHoffmanProof.ABPKperf

/-!
# The `K^{perf}` → `K` descent of Dac §5.2 / Chang Prop. 4.3.1

(Continuation of `AbpDescent.lean`; that file contains the "second relation" `tm_second_relation`
and the sparsification `descent_sparse`.)

This file assembles the descent:

* `ABP_criterion_of_fintype_kperf` — the ABP criterion with `K^{perf}`-coefficients for an
  arbitrary finite index type;
* `exists_pow_eq_of_mem_ambKperf` — `K^{perf}` is perfect (closed under `q`-th roots);
* `tmAOpt_coeff_mem_ambA0` and friends — the `A_0`-coefficient bookkeeping;
* `descent_dependence` — the descent itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-! ## §1. The ABP criterion with `K^{perf}`-coefficients for a general index type -/

section ReindexK

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

/-- The Anderson–Brownawell–Papanikolas criterion with `K^{perf}`-coefficients, for an arbitrary
finite index type. -/
theorem ABP_criterion_of_fintype_kperf (ν : ℕ)
    (hℓ : 2 ≤ Fintype.card ι) (hJ : Fintype.card J = Fintype.card ι - 1)
    {Φ : Matrix ι ι (Polynomial (Ambient F))}
    (hΦ : ∀ i j m, (Φ i j).coeff m ∈ ambA F ν)
    {ϑ : Matrix ι J (Ambient F)} (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1)
    {ψ : ι → PowerSeries (Ambient F)} (hse : ∀ i, GSuperEntire γ (ψ i))
    (hfe : ψ = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ))
    (hind : LinearIndependent (Ambient F) (fun j : J => fun i : ι => ϑ i j))
    {ρ : ι → Ambient F} (hρ : Matrix.vecMul ρ ϑ = 0) (hρ0 : ρ ≠ 0)
    (hρmem : ∀ j, ρ j ∈ ambKperf F)
    (hval : dotProduct ρ (fun i => evalSeriesGen (ψ i) (ambTheta F)) = 0)
    {c : Ambient F} (hc : c ≠ 0) {s : ℕ}
    (hdet : Φ.det = Polynomial.C c * (Polynomial.X - Polynomial.C (ambTheta F)) ^ s) :
    ∃ P : ι → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j) * ψ j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = ρ j) ∧ (∀ j m, (P j).coeff m ∈ ambKperf F) := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with hedef
  set eJ : J ≃ Fin (Fintype.card ι - 1) := Fintype.equivFinOfCardEq hJ with heJdef
  let Φ' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Polynomial (Ambient F)) :=
    Φ.submatrix (⇑e.symm) (⇑e.symm)
  let ψ' : Fin (Fintype.card ι) → PowerSeries (Ambient F) := fun i => ψ (e.symm i)
  let ρ' : Fin (Fintype.card ι) → Ambient F := fun i => ρ (e.symm i)
  let ϑ' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι - 1)) (Ambient F) :=
    fun i j => ϑ (e.symm i) (eJ.symm j)
  have hΦ' : ∀ i j m, (Φ' i j).coeff m ∈ ambA F ν := fun i j m => hΦ _ _ _
  have hϑ' : ∀ i j, ϑ' i j ∈ ambA F ν := fun i j => hϑ _ _
  have hse' : ∀ i, GSuperEntire γ (ψ' i) := fun i => hse (e.symm i)
  have hfe' : ψ' = (frobTwistMat (q := Nat.card F) 1
      ((coeHom (K := Ambient F)).mapMatrix Φ')).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ') := by
    have hN : frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ')
        = (frobTwistMat (q := Nat.card F) 1
            ((coeHom (K := Ambient F)).mapMatrix Φ)).submatrix (⇑e.symm) (⇑e.symm) := by
      ext i j
      simp [Φ', frobTwistMat, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.submatrix_apply]
    have hv : frobTwistVec (q := Nat.card F) 1 ψ'
        = (frobTwistVec (q := Nat.card F) 1 ψ) ∘ (⇑e.symm) := by
      funext i; simp [ψ', frobTwistVec_apply]
    have hvec := submatrix_mulVec_comp_equiv
      (A := frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ))
      (v := frobTwistVec (q := Nat.card F) 1 ψ) (e := e.symm)
    rw [hN, hv, hvec, ← hfe]
    rfl
  have hind' : LinearIndependent (Ambient F)
      (fun j : Fin (Fintype.card ι - 1) => fun i : Fin (Fintype.card ι) => ϑ' i j) := by
    have hv : LinearIndependent (Ambient F)
        (fun t : J => fun i : Fin (Fintype.card ι) => ϑ (e.symm i) t) :=
      linearIndependent_precomp_equiv (v := fun j : J => fun i : ι => ϑ i j) hind e.symm
    have h2 := hv.comp (⇑eJ.symm) eJ.symm.injective
    simpa [ϑ', Function.comp_def] using h2
  have hρ' : Matrix.vecMul ρ' ϑ' = 0 := by
    have h1 : ϑ' = ϑ.submatrix (⇑e.symm) (⇑eJ.symm) := rfl
    have h2 : (ρ' ∘ (⇑e : ι → Fin (Fintype.card ι))) = ρ := by funext k; simp [ρ']
    have h3 := submatrix_vecMul_equiv (M := ϑ) (v := ρ') (e₁ := e.symm)
      (e₂ := (⇑eJ.symm : Fin (Fintype.card ι - 1) → J))
    rw [h1, h3, Equiv.symm_symm, h2, hρ]
    funext j
    rfl
  have hρ0' : ρ' ≠ 0 := by
    intro h
    refine hρ0 (funext fun i => ?_)
    have := congrFun h (e i)
    simpa [ρ'] using this
  have hρmem' : ∀ j, ρ' j ∈ ambKperf F := fun j => hρmem _
  have hval' : dotProduct ρ' (fun i => evalSeriesGen (ψ' i) (ambTheta F)) = 0 := by
    have h1 : ρ' = ρ ∘ (⇑e.symm) := by funext i; simp [ρ']
    have h2 : (fun i => evalSeriesGen (ψ' i) (ambTheta F))
        = (fun i : ι => evalSeriesGen (ψ i) (ambTheta F)) ∘ (⇑e.symm) := by
      funext i; simp [ψ']
    have hEq : dotProduct ρ' (fun i => evalSeriesGen (ψ' i) (ambTheta F))
        = dotProduct ρ (fun i : ι => evalSeriesGen (ψ i) (ambTheta F)) := by
      rw [h1, h2]
      exact comp_equiv_dotProduct_comp_equiv (x := ρ)
        (y := fun i : ι => evalSeriesGen (ψ i) (ambTheta F)) e.symm
    rw [hEq, hval]
  have hdet' : Φ'.det = Polynomial.C c * (Polynomial.X - Polynomial.C (ambTheta F)) ^ s := by
    have h1 : Φ' = Φ.submatrix (⇑e.symm) (⇑e.symm) := rfl
    rw [h1, Matrix.det_submatrix_equiv_self e.symm Φ, hdet]
  obtain ⟨P', hP'1, hP'2, hP'3⟩ :=
    ABP_criterion_kperf F ν hℓ hΦ' hϑ' hγ0 hγ hse' hfe' hind'
      hρ' hρ0' hρmem' hval' hc hdet'
  refine ⟨fun i => P' (e i), ?_, ?_, ?_⟩
  · have hsum : (∑ j : ι, coeHom (K := Ambient F) (P' (e j)) * ψ j)
        = ∑ k : Fin (Fintype.card ι), coeHom (K := Ambient F) (P' k) * ψ' k :=
      Fintype.sum_equiv e _ _ (fun j => by simp [ψ'])
    rw [hsum, hP'1]
  · intro j
    have := hP'2 (e j)
    simpa [ρ'] using this
  · intro j m
    exact hP'3 (e j) m

end ReindexK

/-! ## §2. `K^{perf}` is perfect -/

section Perfect

/-- `(-1) ^ q = -1` for a Frobenius exponent `q`: in characteristic two this is trivial and in odd
characteristic `q` is a power of an odd prime; in both cases additivity gives it directly. -/
lemma frobPow_neg_one {R : Type*} [CommRing R] {q : ℕ} [FrobPow R q] : (-1 : R) ^ q = -1 := by
  have h1 := FrobPow.add_pow (R := R) (q := q) 1 (-1)
  rw [add_neg_cancel, zero_pow (FrobPow.ne_zero R (q := q)), one_pow] at h1
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h1.symm)

/-- **`K^{perf}` is perfect**: every element of `K^{perf}` has a `q`-th root in `K^{perf}`.  The
elements admitting such a root form a subfield containing the generators of `K^{perf}`. -/
theorem exists_pow_eq_of_mem_ambKperf {x : Ambient F} (hx : x ∈ ambKperf F) :
    ∃ y ∈ ambKperf F, y ^ Nat.card F = x := by
  have hq : Nat.card F ≠ 0 := FrobPow.ne_zero (Ambient F) (q := Nat.card F)
  haveI := frobPow_ambient F
  refine Subfield.closure_induction
    (p := fun x (_ : x ∈ ambKperf F) => ∃ y ∈ ambKperf F, y ^ Nat.card F = x)
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · rintro x (⟨c, rfl⟩ | ⟨ν, rfl⟩)
    · exact ⟨ambCoeff F c, ambCoeff_mem_ambKperf F c, by rw [← map_pow, pow_card_eq]⟩
    · exact ⟨ambThetaNu F (ν + 1), ambThetaNu_mem_ambKperf F (ν + 1),
        by simpa using ambThetaNu_pow_add F ν 1⟩
  · exact ⟨1, (ambKperf F).one_mem, by rw [one_pow]⟩
  · rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, (ambKperf F).add_mem ha hb, by rw [FrobPow.add_pow]⟩
  · rintro x _ ⟨a, ha, rfl⟩
    refine ⟨-a, (ambKperf F).neg_mem ha, ?_⟩
    rw [neg_pow, frobPow_neg_one, neg_one_mul]
  · rintro x _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, (ambKperf F).inv_mem ha, by rw [inv_pow]⟩
  · rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, (ambKperf F).mul_mem ha hb, by rw [mul_pow]⟩

/-- Iterated roots: every element of `K^{perf}` has a `q ^ N`-th root in `K^{perf}`. -/
lemma exists_pow_pow_eq_of_mem_ambKperf {x : Ambient F} (hx : x ∈ ambKperf F) (N : ℕ) :
    ∃ y ∈ ambKperf F, y ^ (Nat.card F ^ N) = x := by
  induction N with
  | zero => exact ⟨x, hx, by simp⟩
  | succ N ih =>
    obtain ⟨y, hy, hyx⟩ := ih
    obtain ⟨z, hz, hzy⟩ := exists_pow_eq_of_mem_ambKperf F hy
    exact ⟨z, hz, by rw [pow_succ, mul_comm, pow_mul, hzy, hyx]⟩

end Perfect
