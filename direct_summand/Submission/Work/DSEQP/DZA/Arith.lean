/-
# Area DZA: the chart ring `Away 𝒜 (xS S)` as the degree-zero part of the chart localization

`Work.DSEQP.gf_degzero_away`: there is an `A`-linear isomorphism, natural in `S`, between
`(A[x₀,…,x_N][1/x_S])₀` and `Away (MvPolynomial.homogeneousSubmodule (Fin (N+1)) A) (xS S)`.
The map is the obvious one on the generating fractions `m / xS S ^ k` with `m ∈ 𝒜 (k · S.card)`.
-/
import Submission.Work.DSEQP.DZA.Vocab

open MvPolynomial HomogeneousLocalization
open scoped BigOperators

namespace Work.DSEQP.DZA

universe a

variable {A : Type a} [CommRing A] {N : ℕ}

noncomputable section

/-! ## The `R`-module structure of `R = A[x₀,…,x_N]` over itself -/

/-- The `R`-module structure of `R = A[x₀,…,x_N]` over itself is multiplication. -/
@[local simp] lemma smul_self_eq_mul {r m : MvPolynomial (Fin (N + 1)) A} : r • m = r * m := by
  rw [Algebra.smul_def, Algebra.algebraMap_self_apply]

/-! ## 1. Regularity of `xS S` and of elements of the submonoid `subS S` -/

lemma xS_eq_monomial (S : Finset (Fin (N + 1))) :
    Work.DSEQP.xS (A := A) S = Work.DSCOH.monomial (A := A) (n := N + 1) S := rfl

lemma xS_mem_subS (S : Finset (Fin (N + 1))) :
    Work.DSEQP.xS (A := A) S ∈ Work.DSCOH.subS (A := A) (n := N + 1) S :=
  Work.DSCOH.monomial_mem S

lemma isRegular_xS (S : Finset (Fin (N + 1))) : IsRegular (Work.DSEQP.xS (A := A) S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (isRegular_one : IsRegular (1 : MvPolynomial (Fin (N + 1)) A))
  | insert b s hb ih =>
      have h : Work.DSEQP.xS (A := A) (insert b s) =
          MvPolynomial.X b * Work.DSEQP.xS (A := A) s := by
        simp only [Work.DSEQP.xS, Finset.prod_insert hb]
      rw [h]
      exact IsRegular.mul (MvPolynomial.isRegular_X (R := A) (n := b)) ih

lemma isRegular_of_mem_subS (S : Finset (Fin (N + 1))) {u : MvPolynomial (Fin (N + 1)) A}
    (hu : u ∈ Work.DSCOH.subS (A := A) (n := N + 1) S) : IsRegular u := by
  classical
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, -, hix⟩ := hx
      rw [← hix]
      exact MvPolynomial.isRegular_X (R := A) (n := i)
  | one => exact isRegular_one
  | mul x y _ _ ihx ihy => exact IsRegular.mul ihx ihy

lemma isRegular_of_mem_powers {f : MvPolynomial (Fin (N + 1)) A} (hreg : IsRegular f)
    {c : MvPolynomial (Fin (N + 1)) A} (hc : c ∈ Submonoid.powers f) : IsRegular c := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff c f).mp hc
  exact hreg.pow n

lemma isRegular_xS_pow (S : Finset (Fin (N + 1))) (k : ℕ) :
    IsRegular ((Work.DSEQP.xS (A := A) S) ^ k) := (isRegular_xS S).pow k

/-! ## 2. The chart localization `locAt S` of the polynomial ring at itself -/

/-- The explicit fraction description of `divPow S k (toLoc S m)`. -/
lemma divPow_toLoc_eq_mk (S : Finset (Fin (N + 1))) (k : ℕ)
    (m : MvPolynomial (Fin (N + 1)) A) :
    Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m) =
      LocalizedModule.mk (R := MvPolynomial (Fin (N + 1)) A)
        (S := Work.DSCOH.subS (A := A) (n := N + 1) S) (M := MvPolynomial (Fin (N + 1)) A) m
        ⟨(Work.DSEQP.xS (A := A) S) ^ k,
          Submonoid.pow_mem (Work.DSCOH.subS (A := A) (n := N + 1) S)
            (Work.DSCOH.monomial_mem S) k⟩ := by
  unfold Work.DSCOH.divPow Work.DSCOH.toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]
  exact congrArg _ (Subtype.ext rfl)

/-- **Equality in the chart localization.** -/
lemma locAt_divPow_eq_iff (S : Finset (Fin (N + 1))) (k k' : ℕ)
    (m m' : MvPolynomial (Fin (N + 1)) A) :
    Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m)
      = Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k'
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m')
    ↔ (Work.DSEQP.xS (A := A) S) ^ k' * m = (Work.DSEQP.xS (A := A) S) ^ k * m' := by
  rw [divPow_toLoc_eq_mk, divPow_toLoc_eq_mk, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨u, hu⟩
    have hreg := isRegular_of_mem_subS S u.2
    have hu' : ((u : Work.DSCOH.subS (A := A) (n := N + 1) S) : MvPolynomial (Fin (N + 1)) A)
          * ((Work.DSEQP.xS (A := A) S) ^ k' * m)
        = ((u : Work.DSCOH.subS (A := A) (n := N + 1) S) : MvPolynomial (Fin (N + 1)) A)
          * ((Work.DSEQP.xS (A := A) S) ^ k * m') := by
      simpa only [Submonoid.smul_def, Subtype.coe_mk, smul_self_eq_mul] using hu
    exact IsRegular.left hreg hu'
  · rintro h
    refine ⟨1, ?_⟩
    simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul, smul_self_eq_mul] using h

/-- Addition of two chart fractions, written at the common index `k + k'`. -/
lemma divPow_toLoc_add (S : Finset (Fin (N + 1))) (k k' : ℕ)
    (m m' : MvPolynomial (Fin (N + 1)) A) :
    Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m)
      + Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k'
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m')
    = Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S (k + k')
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S
          ((Work.DSEQP.xS (A := A) S) ^ k' * m + (Work.DSEQP.xS (A := A) S) ^ k * m')) := by
  rw [divPow_toLoc_eq_mk, divPow_toLoc_eq_mk, divPow_toLoc_eq_mk,
    LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, Subtype.coe_mk, smul_self_eq_mul, OneMemClass.coe_one, one_smul,
    Submonoid.coe_mul]
  rw [pow_add]

/-- Scalar multiplication of a chart fraction. -/
lemma divPow_toLoc_smul (S : Finset (Fin (N + 1))) (k : ℕ) (c : A)
    (m : MvPolynomial (Fin (N + 1)) A) :
    c • (Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m))
      = Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S (c • m)) := by
  rw [← LinearMap.map_smul (Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k),
    ← LinearMap.map_smul (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S)]

/-! ## 3. Arithmetic in the chart ring `Away 𝒜 (xS S)` -/

/-- `Away.mk` does not depend on the proof that the element `f` is homogeneous at some degree. -/
lemma away_mk_congr_deg {f : MvPolynomial (Fin (N + 1)) A} {d d' : ℕ}
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) d)
    (hf' : f ∈ Work.DSCOH.homSub A (N + 1) d') (k : ℕ)
    (a : MvPolynomial (Fin (N + 1)) A)
    (ha : a ∈ Work.DSCOH.homSub A (N + 1) (k • d))
    (ha' : a ∈ Work.DSCOH.homSub A (N + 1) (k • d')) :
    Away.mk (DSMap.PGr A N) hf k a ha = Away.mk (DSMap.PGr A N) hf' k a ha' := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]

/-- `Away.mk` depends on the numerator only. -/
lemma away_mk_congr_num {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) d) (k : ℕ)
    {a a' : MvPolynomial (Fin (N + 1)) A} (h : a = a')
    (ha : a ∈ Work.DSCOH.homSub A (N + 1) (k • d))
    (ha' : a' ∈ Work.DSCOH.homSub A (N + 1) (k • d)) :
    Away.mk (DSMap.PGr A N) hf k a ha = Away.mk (DSMap.PGr A N) hf k a' ha' := by
  subst h
  exact congrArg (fun hh => Away.mk (DSMap.PGr A N) hf k a hh) (Subsingleton.elim _ _)

lemma away_mk_congr_idx {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) d) {n n' : ℕ} (hn : n = n')
    {a : MvPolynomial (Fin (N + 1)) A}
    (ha : a ∈ Work.DSCOH.homSub A (N + 1) (n • d))
    (ha' : a ∈ Work.DSCOH.homSub A (N + 1) (n' • d)) :
    Away.mk (DSMap.PGr A N) hf n a ha = Away.mk (DSMap.PGr A N) hf n' a ha' := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  exact congrArg (Localization.mk a) (Subtype.ext (by rw [hn]))


/-- **The fraction description of equality in `Away 𝒜 f`** (for a regular homogeneous `f`). -/
lemma away_mk_eq_iff {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) d) (hreg : IsRegular f) (k k' : ℕ)
    (a a' : MvPolynomial (Fin (N + 1)) A)
    (ha : a ∈ Work.DSCOH.homSub A (N + 1) (k • d))
    (ha' : a' ∈ Work.DSCOH.homSub A (N + 1) (k' • d)) :
    Away.mk (DSMap.PGr A N) hf k a ha = Away.mk (DSMap.PGr A N) hf k' a' ha'
      ↔ f ^ k' * a = f ^ k * a' := by
  rw [← (HomogeneousLocalization.val_injective (Submonoid.powers f)).eq_iff,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  constructor
  · rintro ⟨c, hc⟩
    exact IsRegular.left (isRegular_of_mem_powers hreg c.2) (by
      simpa only [Submonoid.smul_def, Subtype.coe_mk] using hc)
  · rintro h
    exact ⟨1, by simpa only [OneMemClass.coe_one, one_mul] using h⟩

/-- `Away.mk hf 0 0 = 0`. -/
lemma away_mk_zero {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) d) (h : (0 : MvPolynomial (Fin (N + 1)) A) ∈
      Work.DSCOH.homSub A (N + 1) (0 • d)) :
    Away.mk (DSMap.PGr A N) hf 0 0 h = 0 := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_zero]

/-- **Additivity of `Away.mk` at a common index.** -/
lemma away_mk_add_pad {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) d) (k k' : ℕ)
    (a a' : MvPolynomial (Fin (N + 1)) A)
    (ha : a ∈ Work.DSCOH.homSub A (N + 1) (k • d))
    (ha' : a' ∈ Work.DSCOH.homSub A (N + 1) (k' • d))
    (hN : a * f ^ k' + a' * f ^ k ∈ Work.DSCOH.homSub A (N + 1) ((k + k') • d)) :
    Away.mk (DSMap.PGr A N) hf k a ha + Away.mk (DSMap.PGr A N) hf k' a' ha'
      = Away.mk (DSMap.PGr A N) hf (k + k') (a * f ^ k' + a' * f ^ k) hN := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.val_add, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.add_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, Subtype.coe_mk]
  rw [pow_add]
  ring

/-- **Multiplication of `Away.mk`.** -/
lemma away_mk_mul {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) d) (k k' : ℕ)
    (a a' : MvPolynomial (Fin (N + 1)) A)
    (ha : a ∈ Work.DSCOH.homSub A (N + 1) (k • d))
    (ha' : a' ∈ Work.DSCOH.homSub A (N + 1) (k' • d))
    (hN : a * a' ∈ Work.DSCOH.homSub A (N + 1) ((k + k') • d)) :
    Away.mk (DSMap.PGr A N) hf k a ha * Away.mk (DSMap.PGr A N) hf k' a' ha'
      = Away.mk (DSMap.PGr A N) hf (k + k') (a * a') hN := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, Subtype.coe_mk]
  rw [pow_add]

/-- **Scalar multiplication of `Away.mk`** (`c •` is the `A`-module structure of the chart ring,
which is multiplication by the image of `c`). -/
lemma away_mk_smul {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f ∈ Work.DSCOH.homSub A (N + 1) d) (k : ℕ) (c : A)
    (a : MvPolynomial (Fin (N + 1)) A)
    (ha : a ∈ Work.DSCOH.homSub A (N + 1) (k • d)) (ha' : c • a ∈
      Work.DSCOH.homSub A (N + 1) (k • d)) :
    c • (Away.mk (DSMap.PGr A N) hf k a ha)
      = Away.mk (DSMap.PGr A N) hf k (c • a) ha' := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.smul_mk]

end

end Work.DSEQP.DZA
