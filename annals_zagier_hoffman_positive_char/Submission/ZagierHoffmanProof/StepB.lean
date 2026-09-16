import Submission.ZagierHoffmanProof.D2
import Submission.ZagierHoffmanProof.PowerSum

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step B : lifting the level-one shuffle identity to arbitrary `d`

`PowerSum.lean` carries the pending statement `thakur_prod_one` (paper (2.1)) for
general `d`, whose proof needs the level-one content of `D1.lean`/`D2.lean`.  Since
`PowerSum` is at the bottom of the import chain, the general proof (and its
machinery) must live in a module that imports both: this one.

## B2 (transversal description of Thakur's translation classes)

For a monic degree-`< d` polynomial `m` (`e := natDegree m`), the translation action
`x ↦ p + x·m` (`x : F`) partitions the monic degree-`d` polynomials into classes of
`q` elements: adding `x·m` changes the degree-`e` coefficient of `p` by `x` (as `m`
is monic, `coeff_e m = 1`), so the canonical representative of the class of `p` pins
that coefficient to `0`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The class offset of `p` w.r.t. `m`: the degree-`deg m` coefficient of `p`. -/
def clsOffset (d : ℕ) (m : MonicLt F d) (p : HeadD F d) : F :=
  p.1.coeff m.1.natDegree

/-- The canonical representative of the translation class of `p` modulo `F·m`: `m` is
monic of degree `e < d`, and `p + x·m` changes the degree-`e` coefficient by `x`, so
we pin it to `0`. -/
noncomputable def clsRep (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (p : HeadD F d) : F[X] :=
  p.1 - Polynomial.C (clsOffset F d m p) * m.1

/-- For `m` monic of degree `< d`, the polynomial `C c·m` has degree `< d`. -/
lemma shift_tail_natDegree_lt (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (c : F) :
    (Polynomial.C c * m.1).natDegree < d := by
  by_cases hc : c = 0
  · subst c
    simp
    omega
  · rw [Polynomial.natDegree_C_mul (a := c) (p := m.1) (a0 := hc)]
    exact m.2.2

/-- Subtracting a polynomial of degree `< d` keeps `p` monic of degree `d`. -/
lemma monic_sub_of_natDegree_lt (d : ℕ) (hd : 1 ≤ d) (p : HeadD F d) (t : F[X])
    (ht : t.natDegree < d) : (p.1 - t).Monic ∧ (p.1 - t).natDegree = d := by
  have hpd : p.1.natDegree = d := p.2.2
  have hnt : (-t).natDegree < d := by
    rw [Polynomial.natDegree_neg]
    exact ht
  have hdegsum : (p.1 - t).natDegree = p.1.natDegree := by
    change (p.1 + (-t)).natDegree = p.1.natDegree
    exact Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega)
  have hm : (p.1 - t).Monic := by
    rw [Polynomial.Monic.def]
    change (p.1 - t).coeff ((p.1 - t).natDegree) = 1
    rw [hdegsum]
    rw [Polynomial.coeff_sub]
    have hc1 : p.1.coeff p.1.natDegree = 1 := p.2.1.coeff_natDegree
    have hc2 : t.coeff p.1.natDegree = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hc1, hc2]
    simp
  exact ⟨hm, by rw [hdegsum, hpd]⟩

/-- `clsRep` is monic of degree `d`. -/
lemma clsRep_monic_deg (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (p : HeadD F d) :
    (clsRep F d hd m p).Monic ∧ (clsRep F d hd m p).natDegree = d := by
  exact monic_sub_of_natDegree_lt F d hd p (Polynomial.C (clsOffset F d m p) * m.1)
    (shift_tail_natDegree_lt F d hd m (clsOffset F d m p))

/-- The representative pins the degree-`deg m` coefficient to `0`. -/
lemma clsRep_coeff_offset_zero (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (p : HeadD F d) :
    (clsRep F d hd m p).coeff m.1.natDegree = 0 := by
  unfold clsRep clsOffset
  rw [Polynomial.coeff_sub]
  rw [Polynomial.coeff_C_mul (p := m.1)]
  have hcm : m.1.coeff m.1.natDegree = 1 := m.2.1.coeff_natDegree
  rw [hcm]
  ring

/-- Reconstruction: `p = rep(p) + offset(p)·m`. -/
lemma clsRep_add_offset (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (p : HeadD F d) :
    clsRep F d hd m p + Polynomial.C (clsOffset F d m p) * m.1 = p.1 := by
  unfold clsRep clsOffset
  ring


/-- Monic degree-`d` polynomials decompose uniquely as `n + x·m`, where `n` is the
canonical representative of the translation class (degree-`deg m` coefficient `0`)
and `x : F`.  Each class has exactly `|F|` elements. -/
noncomputable def headClassEquiv (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) :
    HeadD F d ≃ {n : HeadD F d // n.1.coeff m.1.natDegree = 0} × F where
  toFun p := (⟨⟨clsRep F d hd m p, by
        change (clsRep F d hd m p).Monic ∧ (clsRep F d hd m p).natDegree = d
        exact clsRep_monic_deg F d hd m p⟩,
      clsRep_coeff_offset_zero F d hd m p⟩, clsOffset F d m p)
  invFun y := ⟨y.1.1.1 + Polynomial.C y.2 * m.1, by
      change (y.1.1.1 + Polynomial.C y.2 * m.1).Monic ∧
        (y.1.1.1 + Polynomial.C y.2 * m.1).natDegree = d
      exact shift_monic F d hd y.1.1 m y.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    change clsRep F d hd m p + Polynomial.C (clsOffset F d m p) * m.1 = p.1
    exact clsRep_add_offset F d hd m p
  right_inv := by
    intro y
    rcases y with ⟨n, x⟩
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      dsimp [clsRep, clsOffset]
      have hcoeff : (n.1.1 + Polynomial.C x * m.1).coeff m.1.natDegree = x := by
        rw [Polynomial.coeff_add]
        rw [Polynomial.coeff_C_mul (p := m.1)]
        rw [n.2]
        rw [m.2.1.coeff_natDegree]
        simp
      rw [hcoeff]
      ring
    · dsimp [clsOffset]
      have hcoeff : (n.1.1 + Polynomial.C x * m.1).coeff m.1.natDegree = x := by
        rw [Polynomial.coeff_add]
        rw [Polynomial.coeff_C_mul (p := m.1)]
        rw [n.2]
        rw [m.2.1.coeff_natDegree]
        simp
      exact hcoeff

/-- The element of the translation class of the representative `n` with offset `x`. -/
noncomputable def classShiftHead (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d)
    (n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0}) (x : F) : HeadD F d :=
  ⟨n.1.1 + Polynomial.C x * m.1, by
    change (n.1.1 + Polynomial.C x * m.1).Monic ∧ (n.1.1 + Polynomial.C x * m.1).natDegree = d
    exact shift_monic F d hd n.1 m x⟩

/-- Summing over all heads equals summing over representatives and offsets. -/
lemma sum_heads_eq_sum_classes (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d)
    (f : HeadD F d → RatFunc F) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ p : HeadD F d, f p) =
      ∑ n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0},
        ∑ x : F, f (classShiftHead F d hd m n x) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let e : HeadD F d ≃ {n : HeadD F d // n.1.coeff m.1.natDegree = 0} × F :=
    headClassEquiv F d hd m
  calc
    (∑ p : HeadD F d, f p)
        = ∑ r : {n : HeadD F d // n.1.coeff m.1.natDegree = 0} × F, f (e.symm r) := by
          exact (Equiv.sum_comp (e := e.symm) f).symm
    _ = ∑ n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0},
          ∑ x : F, f (e.symm (n, x)) := by
          exact Fintype.sum_prod_type (fun r => f (e.symm r))
    _ = ∑ n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0},
          ∑ x : F, f (classShiftHead F d hd m n x) := by
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.sum_congr rfl
          intro x hx
          change f (classShiftHead F d hd m n x) = f (classShiftHead F d hd m n x)
          rfl

/-- Reindexing the offset sum: `Σ_{δ≠0} f (x+δ) = Σ_{y≠x} f y`. -/
lemma sum_erase_add_shift (x : F) (f : F → RatFunc F) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ δ ∈ (Finset.univ : Finset F).erase 0, f (x + δ)) =
      ∑ y ∈ (Finset.univ : Finset F).erase x, f y := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let s : Finset F := (Finset.univ : Finset F).erase 0
  let t : Finset F := (Finset.univ : Finset F).erase x
  refine Finset.sum_bij (s := s) (t := t) (f := fun δ => f (x + δ)) (g := fun y => f y)
    (i := fun (a : F) (_ : a ∈ s) => x + a) ?hi ?i_inj ?i_surj ?h
  · intro a ha
    have ha0 : a ≠ 0 := by simpa [s] using ha
    simp [t]
    intro h
    have h' : x + a = x + 0 := by simpa using h
    have : a = 0 := add_left_cancel h'
    exact ha0 this
  · intro a₁ ha₁ a₂ ha₂ h
    exact add_left_cancel h
  · intro b hb
    have hbx : b ≠ x := by simpa [t] using hb
    refine ⟨b - x, ?_, ?_⟩
    · simp [s]
      intro hz
      apply hbx
      exact eq_of_sub_eq_zero hz
    · ring
  · intro a ha
    rfl

/-- The class power sum `Σ_{x : F} (n + x·m)^{-k}` in `RatFunc F`. -/
noncomputable def clsPowSum (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (n : HeadD F d)
    (k : ℕ) : RatFunc F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  exact ∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ k)⁻¹)

/-- Off-diagonal over a finite type: `Σ_x Σ_{y ≠ x} A x · B y` equals the product of
the sums minus the diagonal. -/
lemma offdiag_eq_prod_sub_diag (A B : F → RatFunc F) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ x : F, ∑ y ∈ (Finset.univ : Finset F).erase x, A x * B y) =
      (∑ x : F, A x) * (∑ x : F, B x) - ∑ x : F, A x * B x := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let S : RatFunc F := ∑ y : F, B y
  have hstep1 : (∑ x : F, ∑ y ∈ (Finset.univ : Finset F).erase x, A x * B y) =
      ∑ x : F, (A x * S - A x * B x) := by
    apply Finset.sum_congr rfl
    intro x hx
    have h := Finset.sum_erase_add (Finset.univ : Finset F) (fun y : F => A x * B y)
      (Finset.mem_univ x)
    have hmain : (∑ y : F, A x * B y) = A x * S := by
      dsimp [S]
      rw [Finset.mul_sum]
    calc
      (∑ y ∈ (Finset.univ : Finset F).erase x, A x * B y)
          = (∑ y : F, A x * B y) - A x * B x := by
            exact eq_sub_of_add_eq h
      _ = A x * S - A x * B x := by rw [hmain]
  calc
    (∑ x : F, ∑ y ∈ (Finset.univ : Finset F).erase x, A x * B y)
        = ∑ x : F, (A x * S - A x * B x) := hstep1
    _ = (∑ x : F, A x * S) - ∑ x : F, (A x * B x) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ x : F, A x) * (∑ x : F, B x) - ∑ x : F, (A x * B x) := by
          rw [Finset.sum_mul]

/-- `clsPowSum` unfolds to its defining sum. -/
lemma clsPowSum_unfold (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (n : HeadD F d) (k : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    clsPowSum F d hd m n k = ∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ k)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  change (∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ k)⁻¹)) =
    (∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ k)⁻¹))
  rfl

/-- In `RatFunc F`, `n + c = (n + c·m)·m⁻¹` whenever `m ≠ 0`. -/
lemma rat_add_div (n m : F[X]) (c : F) (hm : algebraMap F[X] (RatFunc F) m ≠ 0) :
    (algebraMap F[X] (RatFunc F) n) * (algebraMap F[X] (RatFunc F) m)⁻¹ + RatFunc.C c =
      algebraMap F[X] (RatFunc F) (n + Polynomial.C c * m) *
        (algebraMap F[X] (RatFunc F) m)⁻¹ := by
  apply mul_right_cancel₀ hm
  calc
    ((algebraMap F[X] (RatFunc F) n) * (algebraMap F[X] (RatFunc F) m)⁻¹ + RatFunc.C c) *
        (algebraMap F[X] (RatFunc F) m)
        = (algebraMap F[X] (RatFunc F) n) * ((algebraMap F[X] (RatFunc F) m)⁻¹ * (algebraMap F[X] (RatFunc F) m))
            + RatFunc.C c * (algebraMap F[X] (RatFunc F) m) := by ring
    _ = algebraMap F[X] (RatFunc F) n + RatFunc.C c * (algebraMap F[X] (RatFunc F) m) := by
          rw [inv_mul_cancel₀ hm]
          ring
    _ = algebraMap F[X] (RatFunc F) n + algebraMap F[X] (RatFunc F) (Polynomial.C c * m) := by
          rw [← RatFunc.algebraMap_C]
          rw [← map_mul (algebraMap F[X] (RatFunc F)) (Polynomial.C c) m]
    _ = algebraMap F[X] (RatFunc F) (n + Polynomial.C c * m) := by
          rw [← map_add (algebraMap F[X] (RatFunc F)) n (Polynomial.C c * m)]
    _ = (algebraMap F[X] (RatFunc F) (n + Polynomial.C c * m) * (algebraMap F[X] (RatFunc F) m)⁻¹) *
        (algebraMap F[X] (RatFunc F) m) := by
          field_simp [hm]

/-- `(t + c)^{-k} = u^k · (n + c·m)^{-k}` with `t = n/m`, `u = m`. -/
lemma clsPowSum_pow_conv (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (n : HeadD F d)
    (k : ℕ) (c : F) :
    ((((n.1 : RatFunc F) * (m.1 : RatFunc F)⁻¹) + RatFunc.C c) ^ k)⁻¹ =
      ((m.1 : RatFunc F) ^ k) * ((((n.1 + Polynomial.C c * m.1 : F[X]) : RatFunc F) ^ k)⁻¹) := by
  have hm0 : ((m.1 : F[X]) : RatFunc F) ≠ 0 := by
    intro hz
    apply m.2.1.ne_zero
    exact RatFunc.algebraMap_injective F (by simpa using hz)
  have hsplit : ((n.1 : RatFunc F) * (m.1 : RatFunc F)⁻¹) + RatFunc.C c =
      ((n.1 + Polynomial.C c * m.1 : F[X]) : RatFunc F) * (m.1 : RatFunc F)⁻¹ := by
    change algebraMap F[X] (RatFunc F) n.1 * (algebraMap F[X] (RatFunc F) m.1)⁻¹ + RatFunc.C c =
      algebraMap F[X] (RatFunc F) (n.1 + Polynomial.C c * m.1) * (algebraMap F[X] (RatFunc F) m.1)⁻¹
    exact rat_add_div F n.1 m.1 c hm0
  rw [hsplit]
  calc
    ((((n.1 + Polynomial.C c * m.1 : F[X]) : RatFunc F) * (m.1 : RatFunc F)⁻¹) ^ k)⁻¹
        = ((((n.1 + Polynomial.C c * m.1 : F[X]) : RatFunc F) ^ k * ((m.1 : RatFunc F)⁻¹) ^ k))⁻¹ := by rw [mul_pow]
    _ = (((m.1 : RatFunc F)⁻¹) ^ k)⁻¹ * ((((n.1 + Polynomial.C c * m.1 : F[X]) : RatFunc F) ^ k)⁻¹) := by
          rw [mul_inv_rev]
    _ = ((m.1 : RatFunc F) ^ k) * ((((n.1 + Polynomial.C c * m.1 : F[X]) : RatFunc F) ^ k)⁻¹) := by
          congr 1
          have h := inv_pow (m.1 : RatFunc F) k
          rw [h]
          rw [inv_inv]

/-- `t + c ≠ 0` for `t = n/m`: `n + c·m` is monic of degree `d` (hence nonzero) and
`m ≠ 0`. -/
lemma t_add_c_ne_zero (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (n : HeadD F d) (c : F) :
    (n.1 : RatFunc F) * (m.1 : RatFunc F)⁻¹ + RatFunc.C c ≠ 0 := by
  have hnm0 : ((n.1 + Polynomial.C c * m.1 : F[X]) : RatFunc F) ≠ 0 := by
    intro hz
    apply (shift_monic F d hd n m c).1.ne_zero
    exact RatFunc.algebraMap_injective F (by simpa using hz)
  have hm0 : ((m.1 : F[X]) : RatFunc F) ≠ 0 := by
    intro hz
    apply m.2.1.ne_zero
    exact RatFunc.algebraMap_injective F (by simpa using hz)
  have h := rat_add_div F n.1 m.1 c hm0
  change algebraMap F[X] (RatFunc F) n.1 * (algebraMap F[X] (RatFunc F) m.1)⁻¹ + RatFunc.C c ≠ 0
  rw [h]
  exact mul_ne_zero hnm0 (inv_ne_zero hm0)

/-- `aeval t` distributes over the product `∏_c (X + c)`. -/
lemma aeval_prod_add (t : RatFunc F) :
    letI : Fintype F := Fintype.ofFinite F
    (Polynomial.aeval t) (∏ c : F, (Polynomial.X + Polynomial.C c)) =
      ∏ c : F, (t + RatFunc.C c) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let φ : F[X] →* RatFunc F := ((Polynomial.aeval t).toRingHom).toMonoidHom
  have h := map_prod (g := φ) (f := fun c : F => Polynomial.X + Polynomial.C c)
    (Finset.univ : Finset F)
  change φ (∏ c : F, (Polynomial.X + Polynomial.C c)) = ∏ c : F, (t + RatFunc.C c)
  rw [h]
  apply Finset.prod_congr rfl
  intro c hc
  dsimp [φ]
  simp

/-- `[1](n/m) ≠ 0` via the product factorisation. -/
lemma carOne_t_ne_zero (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (n : HeadD F d) :
    letI : Fintype F := Fintype.ofFinite F
    Polynomial.aeval ((n.1 : RatFunc F) * (m.1 : RatFunc F)⁻¹) (carlitzOne F) ≠ 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let t : RatFunc F := (n.1 : RatFunc F) * (m.1 : RatFunc F)⁻¹
  have hc := carlitzOne_eq_prod_X_add_C F
  have haeval : Polynomial.aeval t (carlitzOne F) = ∏ c : F, (t + RatFunc.C c) := by
    rw [hc]
    exact aeval_prod_add F t
  rw [haeval]
  rw [Finset.prod_ne_zero_iff]
  intro c hc'
  exact t_add_c_ne_zero F d hd m n c

/-- `φ := aeval t` maps `A F k` to `[1](t)^k · Σ_c (t + c)^{-k}`, when each
`t + c ≠ 0`. -/
lemma A_aeval_eq (t : RatFunc F) (ht : ∀ c : F, t + RatFunc.C c ≠ 0) (k : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    (Polynomial.aeval t) (A F k) =
      ((Polynomial.aeval t) (carlitzOne F)) ^ k *
        (∑ c : F, (((t + RatFunc.C c) ^ k)⁻¹)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hsplit : (Polynomial.aeval t) (A F k) =
      ∑ c : F, ((Polynomial.aeval t) ((qPoly F c) ^ k)) := by
    calc
      (Polynomial.aeval t) (A F k)
          = (Polynomial.aeval t) (∑ c : F, (qPoly F c) ^ k) := by
            rfl
      _ = ∑ c : F, ((Polynomial.aeval t) ((qPoly F c) ^ k)) := by
            exact map_sum ((Polynomial.aeval t).toAddMonoidHom) (fun c : F => (qPoly F c) ^ k)
              (Finset.univ : Finset F)
  calc
    (Polynomial.aeval t) (A F k)
        = ∑ c : F, ((Polynomial.aeval t) ((qPoly F c) ^ k)) := hsplit
    _ = ∑ c : F, ((Polynomial.aeval t) (qPoly F c)) ^ k := by
          apply Finset.sum_congr rfl
          intro c hc
          exact map_pow ((Polynomial.aeval t).toRingHom) (qPoly F c) k
    _ = ((Polynomial.aeval t) (carlitzOne F)) ^ k * (∑ c : F, (((t + RatFunc.C c) ^ k)⁻¹)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          have hfac : (Polynomial.aeval t) (carlitzOne F) =
              (t + RatFunc.C c) * (Polynomial.aeval t) (qPoly F c) := by
            rw [carlitzOne_eq_mul_qPoly F c]
            have hm : (Polynomial.aeval t) ((Polynomial.X + Polynomial.C c) * qPoly F c) =
                (Polynomial.aeval t) (Polynomial.X + Polynomial.C c) * (Polynomial.aeval t) (qPoly F c) := by
              simpa using (map_mul ((Polynomial.aeval t).toRingHom) (Polynomial.X + Polynomial.C c) (qPoly F c))
            rw [hm]
            simp
          have htk : (t + RatFunc.C c) ^ k ≠ 0 := pow_ne_zero k (ht c)
          have hk := congrArg (fun x : RatFunc F => x ^ k) hfac
          rw [mul_pow] at hk
          rw [eq_comm]
          calc
            ((Polynomial.aeval t) (carlitzOne F)) ^ k * ((t + RatFunc.C c) ^ k)⁻¹
                = ((t + RatFunc.C c) ^ k * (Polynomial.aeval t) (qPoly F c) ^ k) *
                    ((t + RatFunc.C c) ^ k)⁻¹ := by rw [hk]
            _ = (Polynomial.aeval t) (qPoly F c) ^ k := by
                  have hc2 : (t + RatFunc.C c) ^ k * ((t + RatFunc.C c) ^ k)⁻¹ = 1 := mul_inv_cancel₀ htk
                  calc
                    ((t + RatFunc.C c) ^ k * (Polynomial.aeval t) (qPoly F c) ^ k) * ((t + RatFunc.C c) ^ k)⁻¹
                        = (t + RatFunc.C c) ^ k * ((Polynomial.aeval t) (qPoly F c) ^ k * ((t + RatFunc.C c) ^ k)⁻¹) := by ring
                    _ = (t + RatFunc.C c) ^ k * ((t + RatFunc.C c) ^ k)⁻¹ * (Polynomial.aeval t) (qPoly F c) ^ k := by ring
                    _ = 1 * (Polynomial.aeval t) (qPoly F c) ^ k := by rw [hc2]
                    _ = (Polynomial.aeval t) (qPoly F c) ^ k := by simp

/-- `(u^{-1})^{a+b} · u^{a+b-i} = (u^i)^{-1}`. -/
lemma pow_sub_add (u : RatFunc F) (hu : u ≠ 0) (a b i : ℕ) (hle : i ≤ a + b) :
    (u⁻¹) ^ (a + b) * u ^ (a + b - i) = (u ^ i)⁻¹ := by
  have h1 := inv_pow u (a + b)
  rw [h1]
  have hfac : u ^ (a + b - i) * u ^ i = u ^ (a + b) := by
    rw [← pow_add]
    rw [Nat.sub_add_cancel hle]
  apply mul_right_cancel₀ (pow_ne_zero i hu)
  calc
    ((u ^ (a + b))⁻¹ * u ^ (a + b - i)) * u ^ i
        = (u ^ (a + b))⁻¹ * (u ^ (a + b - i) * u ^ i) := by rw [mul_assoc]
    _ = (u ^ (a + b))⁻¹ * u ^ (a + b) := by rw [hfac]
    _ = 1 := by exact inv_mul_cancel₀ (pow_ne_zero (a + b) hu)
    _ = (u ^ i)⁻¹ * u ^ i := by exact (inv_mul_cancel₀ (pow_ne_zero i hu)).symm

/-- `(u^{-1})^k · u^k = 1`. -/
lemma pow_inv_mul_pow (u : RatFunc F) (hu : u ≠ 0) (k : ℕ) :
    (u⁻¹) ^ k * u ^ k = 1 := by
  have h := inv_pow u k
  rw [h]
  exact inv_mul_cancel₀ (pow_ne_zero k hu)

/-- The level-one shuffle read at a general point `t`: with every `t + c ≠ 0` and
`[1](t) ≠ 0`, `(Σ_c (t+c)^{-a})·(Σ_c (t+c)^{-b}) = Σ_c (t+c)^{-(a+b)} +
Σ_{0<i<a+b} Δ^i Σ_c (t+c)^{-(a+b-i)}`. -/
lemma P1rat_t_mul (t : RatFunc F) (htc : ∀ c : F, t + RatFunc.C c ≠ 0)
    (hcar : (Polynomial.aeval t) (carlitzOne F) ≠ 0) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ c : F, (((t + RatFunc.C c) ^ a)⁻¹)) * (∑ c : F, (((t + RatFunc.C c) ^ b)⁻¹)) =
      (∑ c : F, (((t + RatFunc.C c) ^ (a + b))⁻¹)) +
        ∑ i ∈ Finset.Icc 1 (a + b - 1),
          RatFunc.C (ChenDeltaZ F a b i : F) * (∑ c : F, (((t + RatFunc.C c) ^ (a + b - i))⁻¹)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let s : Finset ℕ := Finset.Icc 1 (a + b - 1)
  let h1 : RatFunc F := (Polynomial.aeval t) (carlitzOne F)
  let P := fun k : ℕ => ∑ c : F, (((t + RatFunc.C c) ^ k)⁻¹)
  have hA : ∀ k : ℕ, (Polynomial.aeval t) (A F k) = h1 ^ k * P k := by
    intro k
    dsimp [h1, P]
    exact A_aeval_eq F t htc k
  have hA' : ∀ k : ℕ, ((Polynomial.aeval t).toRingHom) (A F k) = h1 ^ k * P k := by
    intro k
    change (Polynomial.aeval t) (A F k) = h1 ^ k * P k
    exact hA k
  have hP1 := thakurP1 F a b ha hb
  have hmap : (Polynomial.aeval t) (A F a * A F b) =
      (Polynomial.aeval t) (A F (a + b) +
        ∑ i ∈ s, Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) := by
    exact congrArg (Polynomial.aeval t) hP1
  have hL : (Polynomial.aeval t) (A F a * A F b) =
      h1 ^ (a + b) * (P a * P b) := by
    rw [show (Polynomial.aeval t) (A F a * A F b) =
        ((Polynomial.aeval t).toRingHom) (A F a * A F b) by rfl]
    rw [map_mul]
    rw [hA' a, hA' b]
    calc
      h1 ^ a * P a * (h1 ^ b * P b) = (h1 ^ a * h1 ^ b) * (P a * P b) := by ring
      _ = h1 ^ (a + b) * (P a * P b) := by rw [← pow_add]
  have hsum : (∑ i ∈ s, (Polynomial.aeval t)
        (Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))) =
      ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * h1 ^ i * (h1 ^ (a + b - i) * P (a + b - i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    change ((Polynomial.aeval t).toRingHom)
        (Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) =
      RatFunc.C (ChenDeltaZ F a b i : F) * h1 ^ i * (h1 ^ (a + b - i) * P (a + b - i))
    rw [map_mul, map_mul]
    rw [map_pow]
    rw [hA' (a + b - i)]
    dsimp [h1]
    simp
  have hR : (Polynomial.aeval t) (A F (a + b) +
        ∑ i ∈ s, Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) =
      h1 ^ (a + b) * (P (a + b) +
        ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * P (a + b - i)) := by
    calc
      (Polynomial.aeval t) (A F (a + b) +
          ∑ i ∈ s, Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))
          = h1 ^ (a + b) * P (a + b) +
              ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * h1 ^ i *
                (h1 ^ (a + b - i) * P (a + b - i)) := by
            have hma : (Polynomial.aeval t) (A F (a + b) +
                (∑ i ∈ s, Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))) =
                (Polynomial.aeval t) (A F (a + b)) + (Polynomial.aeval t)
                  (∑ i ∈ s, Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) := by
              simpa using (map_add ((Polynomial.aeval t).toAddMonoidHom) (A F (a + b))
                (∑ i ∈ s, Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)))
            rw [hma, hA (a + b)]
            have hms : (Polynomial.aeval t) (∑ i ∈ s,
                Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) =
                ∑ i ∈ s, (Polynomial.aeval t)
                  (Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) := by
              have hmm := map_sum ((Polynomial.aeval t).toAddMonoidHom)
                (fun i : ℕ => Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) s
              simpa using hmm
            rw [hms, hsum]
      _ = h1 ^ (a + b) * P (a + b) +
              ∑ i ∈ s, h1 ^ (a + b) * (RatFunc.C (ChenDeltaZ F a b i : F) * P (a + b - i)) := by
            apply congrArg (fun u : RatFunc F => h1 ^ (a + b) * P (a + b) + u)
            apply Finset.sum_congr rfl
            intro i hi
            calc
              RatFunc.C (ChenDeltaZ F a b i : F) * h1 ^ i * (h1 ^ (a + b - i) * P (a + b - i))
                  = (h1 ^ i * h1 ^ (a + b - i)) * (RatFunc.C (ChenDeltaZ F a b i : F) * P (a + b - i)) := by ring
              _ = h1 ^ (a + b) * (RatFunc.C (ChenDeltaZ F a b i : F) * P (a + b - i)) := by
                    have hle : i ≤ a + b := by
                      have hin : i ≤ a + b - 1 := (Finset.mem_Icc.mp hi).2
                      omega
                    rw [← pow_add]
                    rw [Nat.add_sub_of_le hle]
      _ = h1 ^ (a + b) * (P (a + b) +
              ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * P (a + b - i)) := by
            rw [← Finset.mul_sum]
            ring
  have hboth : h1 ^ (a + b) * (P a * P b) =
      h1 ^ (a + b) * (P (a + b) +
        ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * P (a + b - i)) := by
    rw [← hL, hmap, hR]
  have h1ne : h1 ≠ 0 := by
    dsimp [h1]
    exact hcar
  have hcancel := mul_left_cancel₀ (pow_ne_zero (a + b) h1ne) hboth
  simpa [s, P] using hcancel

/-- The per-class level-one shuffle (`E_m`'s Step 2), in class-power-sum form:
`T_a·T_b = T_{a+b} + Σ_{0<i<a+b} Δ^i m^{-i} T_{a+b-i}` with
`T_k := clsPowSum n k`. -/
lemma clsPowSum_mul (d : ℕ) (hd : 1 ≤ d) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (m : MonicLt F d) (n : HeadD F d) :
    letI : Fintype F := Fintype.ofFinite F
    clsPowSum F d hd m n a * clsPowSum F d hd m n b =
      clsPowSum F d hd m n (a + b) +
      ∑ i ∈ Finset.Icc 1 (a + b - 1),
        RatFunc.C (ChenDeltaZ F a b i : F) * (((m.1 : RatFunc F) ^ i)⁻¹) *
        clsPowSum F d hd m n (a + b - i) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let t : RatFunc F := (n.1 : RatFunc F) * (m.1 : RatFunc F)⁻¹
  let u : RatFunc F := (m.1 : RatFunc F)
  let s : Finset ℕ := Finset.Icc 1 (a + b - 1)
  let T := fun k : ℕ => clsPowSum F d hd m n k
  have htc : ∀ c : F, t + RatFunc.C c ≠ 0 := fun c => by
    dsimp [t]
    exact t_add_c_ne_zero F d hd m n c
  have hcar : (Polynomial.aeval t) (carlitzOne F) ≠ 0 := by
    dsimp [t]
    exact carOne_t_ne_zero F d hd m n
  have hu : u ≠ 0 := by
    dsimp [u]
    intro hz
    apply m.2.1.ne_zero
    exact RatFunc.algebraMap_injective F (by simpa using hz)
  have ht := P1rat_t_mul F t htc hcar a b ha hb
  have hconv : ∀ k : ℕ, (∑ c : F, (((t + RatFunc.C c) ^ k)⁻¹)) = u ^ k * T k := by
    intro k
    dsimp [T]
    rw [clsPowSum_unfold F d hd m n k]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    dsimp [t, u]
    exact clsPowSum_pow_conv F d hd m n k c
  have hinnersum : (∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) *
        (∑ c : F, (((t + RatFunc.C c) ^ (a + b - i))⁻¹))) =
      ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * (u ^ (a + b - i) * T (a + b - i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hconv (a + b - i)]
  let v : RatFunc F := (u⁻¹) ^ (a + b)
  have hboth : v * ((∑ c : F, (((t + RatFunc.C c) ^ a)⁻¹)) *
        (∑ c : F, (((t + RatFunc.C c) ^ b)⁻¹))) =
      v * ((∑ c : F, (((t + RatFunc.C c) ^ (a + b))⁻¹)) +
        ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * (∑ c : F, (((t + RatFunc.C c) ^ (a + b - i))⁻¹))) := by
    dsimp [v]
    rw [ht]
  have hL' : v * ((∑ c : F, (((t + RatFunc.C c) ^ a)⁻¹)) *
        (∑ c : F, (((t + RatFunc.C c) ^ b)⁻¹))) = T a * T b := by
    rw [hconv a, hconv b]
    dsimp [v]
    calc
      (u⁻¹) ^ (a + b) * ((u ^ a * T a) * (u ^ b * T b))
          = (u⁻¹) ^ (a + b) * (u ^ a * u ^ b * (T a * T b)) := by ring
      _ = (u⁻¹) ^ (a + b) * (u ^ (a + b) * (T a * T b)) := by
            rw [← pow_add]
      _ = ((u⁻¹) ^ (a + b) * u ^ (a + b)) * (T a * T b) := by ring
      _ = 1 * (T a * T b) := by
            rw [pow_inv_mul_pow F u hu (a + b)]
      _ = T a * T b := by simp
  have hdist1 : (u⁻¹) ^ (a + b) * (u ^ (a + b) * T (a + b)) = T (a + b) := by
    calc
      (u⁻¹) ^ (a + b) * (u ^ (a + b) * T (a + b))
          = ((u⁻¹) ^ (a + b) * u ^ (a + b)) * T (a + b) := by ring
      _ = T (a + b) := by rw [pow_inv_mul_pow F u hu (a + b)]; simp
  have hterm : ∀ i : ℕ, i ∈ s →
      (u⁻¹) ^ (a + b) * (RatFunc.C (ChenDeltaZ F a b i : F) * (u ^ (a + b - i) * T (a + b - i))) =
      RatFunc.C (ChenDeltaZ F a b i : F) * ((u ^ i)⁻¹) * T (a + b - i) := by
    intro i hi
    calc
      (u⁻¹) ^ (a + b) * (RatFunc.C (ChenDeltaZ F a b i : F) * (u ^ (a + b - i) * T (a + b - i)))
          = RatFunc.C (ChenDeltaZ F a b i : F) * (((u⁻¹) ^ (a + b) * u ^ (a + b - i)) * T (a + b - i)) := by ring
      _ = RatFunc.C (ChenDeltaZ F a b i : F) * (((u ^ i)⁻¹) * T (a + b - i)) := by
            have hle : i ≤ a + b := by
              have hin : i ≤ a + b - 1 := (Finset.mem_Icc.mp hi).2
              omega
            rw [pow_sub_add F u hu a b i hle]
      _ = RatFunc.C (ChenDeltaZ F a b i : F) * ((u ^ i)⁻¹) * T (a + b - i) := by ring
  have hR' : v * ((∑ c : F, (((t + RatFunc.C c) ^ (a + b))⁻¹)) +
        ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * (∑ c : F, (((t + RatFunc.C c) ^ (a + b - i))⁻¹))) =
      T (a + b) + ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * ((u ^ i)⁻¹) * T (a + b - i) := by
    rw [hconv (a + b)]
    rw [hinnersum]
    dsimp [v]
    calc
      (u⁻¹) ^ (a + b) * (u ^ (a + b) * T (a + b) +
          ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * (u ^ (a + b - i) * T (a + b - i)))
          = (u⁻¹) ^ (a + b) * (u ^ (a + b) * T (a + b)) +
              (u⁻¹) ^ (a + b) * (∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * (u ^ (a + b - i) * T (a + b - i))) := by
            rw [mul_add]
      _ = T (a + b) +
              (u⁻¹) ^ (a + b) * (∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * (u ^ (a + b - i) * T (a + b - i))) := by
            rw [hdist1]
      _ = T (a + b) +
              ∑ i ∈ s, (u⁻¹) ^ (a + b) *
                (RatFunc.C (ChenDeltaZ F a b i : F) * (u ^ (a + b - i) * T (a + b - i))) := by
            rw [Finset.mul_sum]
      _ = T (a + b) + ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * ((u ^ i)⁻¹) * T (a + b - i) := by
            apply congrArg (fun z : RatFunc F => T (a + b) + z)
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i hi
  simpa [s, u, T] using (hL'.symm.trans (hboth.trans hR'))

/-- The class-shift element satisfies `(classShiftHead n x).1 + Cδ·m = n + C(x+δ)·m`. -/
lemma classShift_poly_add (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d)
    (n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0}) (x δ : F) :
    (classShiftHead F d hd m n x).1 + Polynomial.C δ * m.1 =
      n.1.1 + Polynomial.C (x + δ) * m.1 := by
  dsimp [classShiftHead]
  calc
    (n.1.1 + Polynomial.C x * m.1) + Polynomial.C δ * m.1
        = n.1.1 + (Polynomial.C x * m.1 + Polynomial.C δ * m.1) := by ring
    _ = n.1.1 + ((Polynomial.C x + Polynomial.C δ) * m.1) := by
          rw [← add_mul]
    _ = n.1.1 + Polynomial.C (x + δ) * m.1 := by
          rw [← Polynomial.C_add]

/-- `E_m` LHS rewritten over translation classes (Step 1):
`Σ_p Σ_{δ≠0} p^{-a}(p+δm)^{-b} = Σ_n Σ_x Σ_{δ≠0} (n+xm)^{-a}(n+(x+δ)m)^{-b}`. -/
lemma E_m_lhs_class (d : ℕ) (hd : 1 ≤ d) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (m : MonicLt F d) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ p : HeadD F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
        (((p.1 : RatFunc F) ^ a)⁻¹) *
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹)) =
      ∑ n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0},
        ∑ x : F, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
          ((((n.1.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ a)⁻¹) *
          ((((n.1.1 + Polynomial.C (x + δ) * m.1 : F[X]) : RatFunc F) ^ b)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  have h := sum_heads_eq_sum_classes F d hd m (fun p : HeadD F d =>
      ∑ δ ∈ (Finset.univ : Finset F).erase 0,
        (((p.1 : RatFunc F) ^ a)⁻¹) *
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹))
  calc
    (∑ p : HeadD F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
        (((p.1 : RatFunc F) ^ a)⁻¹) *
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹))
        = ∑ n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0},
            ∑ x : F, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
              ((((classShiftHead F d hd m n x).1 : RatFunc F) ^ a)⁻¹) *
              (((((classShiftHead F d hd m n x).1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹) := h
    _ = ∑ n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0},
          ∑ x : F, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
            ((((n.1.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ a)⁻¹) *
            ((((n.1.1 + Polynomial.C (x + δ) * m.1 : F[X]) : RatFunc F) ^ b)⁻¹) := by
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro δ hδ
          have h2 : (classShiftHead F d hd m n x).1 + Polynomial.C δ * m.1 =
              n.1.1 + Polynomial.C (x + δ) * m.1 := classShift_poly_add F d hd m n x δ
          have h1 : ((classShiftHead F d hd m n x).1 : RatFunc F) =
              ((n.1.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) := by
            dsimp [classShiftHead]
          rw [h2, h1]

-- Reindexing the representatives: summing `clsPowSum` over all canonical
-- representatives of the translation classes recovers the full sum over `HeadD F d`.
lemma clsPowSum_sum_classes (d : ℕ) (hd : 1 ≤ d) (m : MonicLt F d) (k : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0}, clsPowSum F d hd m n.1 k) =
      ∑ p : HeadD F d, (((p.1 : RatFunc F) ^ k)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  have h := sum_heads_eq_sum_classes F d hd m (fun p : HeadD F d => (((p.1 : RatFunc F) ^ k)⁻¹))
  calc
    (∑ n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0}, clsPowSum F d hd m n.1 k)
        = ∑ n : {n : HeadD F d // n.1.coeff m.1.natDegree = 0},
            ∑ x : F, ((((classShiftHead F d hd m n x).1 : RatFunc F) ^ k)⁻¹) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [clsPowSum_unfold F d hd m n.1 k]
          apply Finset.sum_congr rfl
          intro x hx
          dsimp [classShiftHead]
    _ = ∑ p : HeadD F d, (((p.1 : RatFunc F) ^ k)⁻¹) := by
          exact h.symm

/-- `E_m` (RatFunc form): for a fixed monic `m` of degree `< d`,
`Σ_{p} Σ_{δ ≠ 0} p^{-a} (p + δ·m)^{-b} = Σ_{0<i<a+b} Δ^i m^{-i} Σ_p p^{-(a+b-i)}`. -/
lemma E_m_rat (d : ℕ) (hd : 1 ≤ d) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (m : MonicLt F d) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ p : HeadD F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
        (((p.1 : RatFunc F) ^ a)⁻¹) *
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹)) =
      ∑ i ∈ Finset.Icc 1 (a + b - 1),
        (RatFunc.C (ChenDeltaZ F a b i : F) * (((m.1 : RatFunc F) ^ i)⁻¹)) *
        (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let s : Finset ℕ := Finset.Icc 1 (a + b - 1)
  let u : RatFunc F := (m.1 : RatFunc F)
  let reps := {n : HeadD F d // n.1.coeff m.1.natDegree = 0}
  let er0 : Finset F := (Finset.univ : Finset F).erase 0
  let A := fun (n : HeadD F d) (x : F) =>
      ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ a)⁻¹)
  let B := fun (n : HeadD F d) (x : F) =>
      ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ b)⁻¹)
  let T := fun (n : HeadD F d) (k : ℕ) => clsPowSum F d hd m n k
  have hL := E_m_lhs_class F d hd a b ha hb m
  have hpull : ∀ n : HeadD F d, (∑ x : F, ∑ δ ∈ er0, A n x * B n (x + δ)) =
      ∑ x : F, A n x * (∑ δ ∈ er0, B n (x + δ)) := by
    intro n
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [er0]
    rw [Finset.mul_sum]
  have hshift : ∀ n : HeadD F d, (∑ x : F, A n x * (∑ δ ∈ er0, B n (x + δ))) =
      ∑ x : F, ∑ y ∈ (Finset.univ : Finset F).erase x, A n x * B n y := by
    intro n
    apply Finset.sum_congr rfl
    intro x hx
    have h := sum_erase_add_shift F x (fun y : F => B n y)
    rw [h]
    rw [Finset.mul_sum]
  have hoff (n : HeadD F d) : (∑ x : F, ∑ y ∈ (Finset.univ : Finset F).erase x, A n x * B n y) =
      (∑ x : F, A n x) * (∑ x : F, B n x) - ∑ x : F, (A n x * B n x) := by
    exact offdiag_eq_prod_sub_diag F (fun x : F => A n x) (fun x : F => B n x)
  have hTsumA (n : HeadD F d) : (∑ x : F, A n x) = T n a := by
    dsimp [A, T]
    change (∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ a)⁻¹)) =
      (∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ a)⁻¹))
    rfl
  have hTsumB (n : HeadD F d) : (∑ x : F, B n x) = T n b := by
    dsimp [B, T]
    change (∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ b)⁻¹)) =
      (∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ b)⁻¹))
    rfl
  have hinv (X : RatFunc F) (k l : ℕ) : (X ^ k)⁻¹ * (X ^ l)⁻¹ = (X ^ (k + l))⁻¹ := by
    calc
      (X ^ k)⁻¹ * (X ^ l)⁻¹ = (X ^ k * X ^ l)⁻¹ := by
            rw [mul_comm (X ^ k)⁻¹ (X ^ l)⁻¹]
            exact (mul_inv_rev (X ^ k) (X ^ l)).symm
      _ = (X ^ (k + l))⁻¹ := by rw [pow_add]
  have hDiag (n : HeadD F d) : (∑ x : F, (A n x * B n x)) = T n (a + b) := by
    dsimp [A, B, T]
    change (∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ a)⁻¹ *
          (((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ b)⁻¹)) =
      (∑ x : F, ((((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F) ^ (a + b))⁻¹))
    apply Finset.sum_congr rfl
    intro x hx
    exact hinv (((n.1 + Polynomial.C x * m.1 : F[X]) : RatFunc F)) a b
  have hshuffle (n : HeadD F d) :
      (∑ x : F, A n x) * (∑ x : F, B n x) - ∑ x : F, (A n x * B n x) =
      ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * ((u ^ i)⁻¹) * T n (a + b - i) := by
    have hcm := clsPowSum_mul F d hd a b ha hb m n
    have hcm' : T n a * T n b = T n (a + b) +
        ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * ((u ^ i)⁻¹) * T n (a + b - i) := by
      simpa [s, u, T] using hcm
    calc
      (∑ x : F, A n x) * (∑ x : F, B n x) - ∑ x : F, (A n x * B n x)
          = T n a * T n b - T n (a + b) := by rw [hTsumA n, hTsumB n, hDiag n]
      _ = ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * ((u ^ i)⁻¹) * T n (a + b - i) := by
            rw [hcm']
            ring
  calc
    (∑ p : HeadD F d, ∑ δ ∈ er0,
        (((p.1 : RatFunc F) ^ a)⁻¹) *
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹))
        = ∑ n : reps, ∑ x : F, ∑ δ ∈ er0, A n.1 x * B n.1 (x + δ) := by
          simpa [A, B, er0] using hL
    _ = ∑ n : reps, ∑ x : F, A n.1 x * (∑ δ ∈ er0, B n.1 (x + δ)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hpull n.1
    _ = ∑ n : reps, ∑ x : F, ∑ y ∈ (Finset.univ : Finset F).erase x, A n.1 x * B n.1 y := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hshift n.1
    _ = ∑ n : reps, ((∑ x : F, A n.1 x) * (∑ x : F, B n.1 x) - ∑ x : F, (A n.1 x * B n.1 x)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hoff n.1
    _ = ∑ n : reps, ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * ((u ^ i)⁻¹) * T n.1 (a + b - i) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hshuffle n.1
    _ = ∑ i ∈ s, RatFunc.C (ChenDeltaZ F a b i : F) * ((u ^ i)⁻¹) *
          (∑ n : reps, T n.1 (a + b - i)) := by
          rw [Finset.sum_comm (s := (Finset.univ : Finset reps)) (t := s)]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.Icc 1 (a + b - 1),
          (RatFunc.C (ChenDeltaZ F a b i : F) * (((m.1 : RatFunc F) ^ i)⁻¹)) *
          (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have htot : (∑ n : reps, T n.1 (a + b - i)) =
              ∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹) := by
            simpa [T] using (clsPowSum_sum_classes F d hd m (a + b - i))
          rw [htot]


/-- `E_m_sum` (B3, RatFunc form): summing `E_m` over all monic `m` of degree `< d`,
`Σ_m Σ_p Σ_{δ≠0} p^{-a}(p+δm)^{-b} =
Σ_{0<i<a+b} Δ^i (Σ_m m^{-i})(Σ_p p^{-(a+b-i)})`. -/
lemma E_m_sum (d : ℕ) (hd : 1 ≤ d) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ m : MonicLt F d, ∑ p : HeadD F d, ∑ δ ∈ (Finset.univ : Finset F).erase 0,
        (((p.1 : RatFunc F) ^ a)⁻¹) *
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹)) =
      ∑ i ∈ Finset.Icc 1 (a + b - 1),
        RatFunc.C (ChenDeltaZ F a b i : F) * (∑ m : MonicLt F d, (((m.1 : RatFunc F) ^ i)⁻¹)) *
          (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let s : Finset ℕ := Finset.Icc 1 (a + b - 1)
  let er0 : Finset F := (Finset.univ : Finset F).erase 0
  calc
    (∑ m : MonicLt F d, ∑ p : HeadD F d, ∑ δ ∈ er0,
        (((p.1 : RatFunc F) ^ a)⁻¹) *
        ((((p.1 + Polynomial.C δ * m.1 : F[X]) : RatFunc F) ^ b)⁻¹))
        = ∑ m : MonicLt F d, ∑ i ∈ s,
            (RatFunc.C (ChenDeltaZ F a b i : F) * (((m.1 : RatFunc F) ^ i)⁻¹)) *
            (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹)) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact E_m_rat F d hd a b ha hb m
    _ = ∑ i ∈ s, ∑ m : MonicLt F d,
            (RatFunc.C (ChenDeltaZ F a b i : F) * (((m.1 : RatFunc F) ^ i)⁻¹)) *
            (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹)) := by
          rw [Finset.sum_comm (s := (Finset.univ : Finset (MonicLt F d))) (t := s)]
    _ = ∑ i ∈ s,
          RatFunc.C (ChenDeltaZ F a b i : F) * (∑ m : MonicLt F d, (((m.1 : RatFunc F) ^ i)⁻¹)) *
          (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hin : (∑ m : MonicLt F d,
                (RatFunc.C (ChenDeltaZ F a b i : F) * (((m.1 : RatFunc F) ^ i)⁻¹)) *
                (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹))) =
              (∑ m : MonicLt F d, RatFunc.C (ChenDeltaZ F a b i : F) * (((m.1 : RatFunc F) ^ i)⁻¹)) *
                (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ (a + b - i))⁻¹)) := by
            rw [← Finset.sum_mul]
          have hmul : (∑ m : MonicLt F d, RatFunc.C (ChenDeltaZ F a b i : F) * (((m.1 : RatFunc F) ^ i)⁻¹)) =
              RatFunc.C (ChenDeltaZ F a b i : F) * (∑ m : MonicLt F d, (((m.1 : RatFunc F) ^ i)⁻¹)) := by
            rw [← Finset.mul_sum]
          rw [hin, hmul]

end ZagierHoffmanPositiveChar
