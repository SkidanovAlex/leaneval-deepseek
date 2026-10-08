import Mathlib
import Submission.Work.L2F.Props.Count.Defs
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.Count.Basic
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.L2F.Mat2.quadAlgebra
import Submission.Work.L2F.Involution.mem_normalizer_zpowers
import Submission.Work.L2F.Props.Count.SquareMulNonsquare

/-!
# The number of rootless `t` with `X² - tX + 1 ∣ X^r - 1`

Let `F` be a finite field of odd characteristic, `r ≠ 2` a prime, and `quad t = X² - tX + 1`.
Writing `Rootless F t` for `quad t` having no root in `F` (equivalently `quad t` irreducible), we
prove

`2 * #{t : F | Rootless F t ∧ quad F t ∣ X^r - 1} = if r ∣ (q+1) then r - 1 else 0`.

The proof identifies both sides with the `r`-torsion of a non-split torus.

* For `u ∈ SL(2,F)` in the non-split torus `hypTorus F d` (all of whose elements are matrices
  `!![a, d*b; b, a]`) with non-zero `(1,0)`-entry `b` and `u ^ r = 1`, the trace `t = 2a` is
  rootless and `quad t ∣ X^r - 1`.  Indeed `(a - x)² = d·b²` would make `d` a square for any root
  `x` of `quad t`, and `quad t = charpoly u` is the minimal polynomial of `u`.
* Conversely, for rootless `t` with `quad t ∣ X^r - 1`, the element `c` with `d·c² = t² - 4`
  exists (the non-squares of `F` form a coset of the squares), and
  `u = !![t/2, d·(c/2); c/2, t/2]` is a non-split element of `hypTorus F d` with `u ^ r = 1` and
  trace `t`; its order is therefore `r`.
* Two elements of `hypTorus F d` with the same trace have the same `a`-coordinate, hence
  `b`-coordinates `±b`: they are `u` and `u⁻¹`.  Hence the trace map is exactly `2`-to-`1` from
  the elements of `hypTorus F d` of order `r` onto `{t | Rootless F t ∧ quad F t ∣ X^r - 1}`.
* `hypTorus F d` is cyclic of order `q + 1`, so the number of its elements of order `r` is
  `r - 1` when `r ∣ q+1` and `0` otherwise.
-/

open scoped MatrixGroups
open Matrix Polynomial

namespace Work.L2F.Props.Count

open Work.L2F.Count

variable {F : Type*} [Field F]

/-- The set of `t : F` with `Rootless F t` and `quad F t ∣ X^r - 1`. -/
def SSet (r : ℕ) : Set F := {t | Rootless F t ∧ quad F t ∣ Polynomial.X ^ r - 1}

/-- The set of elements of the non-split torus `hypTorus F d` of order the prime `r`. -/
def TSet (d : F) (r : ℕ) : Set (Matrix.SpecialLinearGroup (Fin 2) F) :=
  {u | u ∈ Work.L2F.hypTorus F d ∧ orderOf u = r}

/-- In any monoid, `x ^ orderOf x = 1`. -/
theorem pow_eq_one_of_orderOf_eq {G : Type*} [Monoid G] {x : G} {r : ℕ} (h : orderOf x = r) :
    x ^ r = 1 := by
  rw [← h]; exact pow_orderOf_eq_one x

/-- An element of `Fin 2` is `0` or `1`. -/
theorem fin2_eq_zero_or_eq_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h := i.isLt
  rcases (by omega : i.val = 0 ∨ i.val = 1) with h0 | h1
  · exact Or.inl (Fin.ext h0)
  · exact Or.inr (Fin.ext h1)

/-! ## Polynomial facts about `quad t = X² - tX + 1` -/

theorem quad_irreducible {t : F} (ht : Rootless F t) : Irreducible (quad F t) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [show quad F t = Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X
        + Polynomial.C 1 by
      simp only [quad, Polynomial.C_neg, Polynomial.C_1]; ring]
    rw [Polynomial.natDegree_quadratic (by norm_num)]
    norm_num
  · intro a ha
    exact ht a ((quad_isRoot_iff t a).mp ha)

theorem aeval_quad_eq_zero (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Polynomial.aeval (x : Matrix (Fin 2) (Fin 2) F)
      (quad F ((x : Matrix (Fin 2) (Fin 2) F).trace)) = 0 := by
  rw [← charpoly_sl x]
  exact Matrix.aeval_self_charpoly _

theorem aeval_X_pow_sub_one (x : Matrix.SpecialLinearGroup (Fin 2) F) (r : ℕ) :
    Polynomial.aeval (x : Matrix (Fin 2) (Fin 2) F)
      ((Polynomial.X : Polynomial F) ^ r - 1) = (x : Matrix (Fin 2) (Fin 2) F) ^ r - 1 := by
  rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one]

/-! ## The forward map: from `hypTorus F d` to rootless traces -/

/-- An element `u` of the non-split torus `hypTorus F d` with non-zero `(1,0)`-entry and
`u ^ r = 1` has rootless trace `t` and `quad t ∣ X^r - 1`. -/
theorem rootless_quad_dvd_of_mem_hypTorus {d : F} (hnsq : ∀ a : F, a * a ≠ d) {r : ℕ}
    {u : Matrix.SpecialLinearGroup (Fin 2) F} (hu : u ∈ Work.L2F.hypTorus F d)
    (hb : (u : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) (hur : u ^ r = 1) :
    Rootless F ((u : Matrix (Fin 2) (Fin 2) F).trace) ∧
      quad F ((u : Matrix (Fin 2) (Fin 2) F).trace) ∣ Polynomial.X ^ r - 1 := by
  obtain ⟨a, b, hab, hu'⟩ := (Work.L2F.Conic.mem_hypTorus F d u).mp hu
  have hb' : b ≠ 0 := by rw [hu'] at hb; simpa using hb
  have htr : (u : Matrix (Fin 2) (Fin 2) F).trace = 2 * a := by
    rw [hu', Matrix.trace_fin_two, two_mul]
    simp
  have hroot : Rootless F ((u : Matrix (Fin 2) (Fin 2) F).trace) := by
    intro x hx
    rw [htr] at hx
    have key : (a - x) ^ 2 = d * b ^ 2 := by linear_combination hab + hx
    have hsq : ((a - x) / b) * ((a - x) / b) = d := by
      rw [div_mul_div_comm]
      rw [show (a - x) * (a - x) = (a - x) ^ 2 by ring, show b * b = b ^ 2 by ring]
      exact (div_eq_iff (pow_ne_zero 2 hb')).mpr key
    exact hnsq ((a - x) / b) hsq
  refine ⟨hroot, ?_⟩
  have hkey : Polynomial.aeval (u : Matrix (Fin 2) (Fin 2) F)
      ((Polynomial.X : Polynomial F) ^ r - 1) = 0 := by
    rw [aeval_X_pow_sub_one]
    have hpow : (u : Matrix (Fin 2) (Fin 2) F) ^ r = 1 := by
      rw [← show ((u ^ r : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = (u : Matrix (Fin 2) (Fin 2) F) ^ r from rfl, hur]
      rfl
    rw [hpow, sub_self]
  exact ((quad_irreducible hroot).dvd_iff_aeval_eq_zero (aeval_quad_eq_zero u)).mp hkey

/-- If `u ∈ hypTorus F d` has order a prime `r ≠ 2`, then its `(1,0)`-entry is non-zero. -/
theorem entry10_ne_zero_of_orderOf_eq {d : F} (h2 : (2 : F) ≠ 0) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {u : Matrix.SpecialLinearGroup (Fin 2) F}
    (hu : u ∈ Work.L2F.hypTorus F d) (ho : orderOf u = r) :
    (u : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
  intro hb
  obtain ⟨a, b, hab, hu'⟩ := (Work.L2F.Conic.mem_hypTorus F d u).mp hu
  have hb0 : b = 0 := by rw [hu'] at hb; simpa using hb
  have ha2 : a ^ 2 = 1 := by
    have h : a ^ 2 - d * b ^ 2 = 1 := hab
    rw [hb0] at h
    simpa using h
  have hu2 : u ^ 2 = 1 := by
    rcases sq_eq_one_iff.mp ha2 with ha | ha
    · have hu1' : (u : Matrix (Fin 2) (Fin 2) F) = 1 := by
        rw [hu', hb0, ha]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [show u = 1 from Subtype.ext hu1']
      exact one_pow 2
    · have hun : u = Work.L2F.negOne F := by
        apply Subtype.ext
        rw [hu', hb0, ha]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Work.L2F.negOne]
      rw [hun]
      exact Work.L2F.Involution.negOne_pow_two F
  have h2dvd : r ∣ 2 := by
    rw [← ho]
    exact orderOf_dvd_iff_pow_eq_one.mpr hu2
  rcases (Nat.dvd_prime Nat.prime_two).mp h2dvd with h | h
  · exact hr.ne_one h
  · exact hr2 h

/-! ## The trace is invariant under inversion on `hypTorus F d` -/

theorem trace_inv_of_mem_hypTorus {d : F} {u : Matrix.SpecialLinearGroup (Fin 2) F}
    (hu : u ∈ Work.L2F.hypTorus F d) :
    ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace
      = (u : Matrix (Fin 2) (Fin 2) F).trace := by
  obtain ⟨a, b, hab, hu'⟩ := (Work.L2F.Conic.mem_hypTorus F d u).mp hu
  rw [Matrix.SpecialLinearGroup.coe_inv, hu', Matrix.adjugate_fin_two_of, Matrix.trace_fin_two]
  simp

/-! ## The converse: every rootless `t` with `quad t ∣ X^r - 1` is the trace of an element of
`hypTorus F d` of order `r` -/

theorem exists_hypTorus_orderOf (F : Type*) [Field F] [Fintype F] {d : F} (h2 : (2 : F) ≠ 0)
    (hd : d ≠ 0) (hnsq : ∀ a : F, a * a ≠ d) {r : ℕ} (hr : r.Prime) {t : F}
    (hroot : Rootless F t) (hdvd : quad F t ∣ Polynomial.X ^ r - 1) :
    ∃ u : Matrix.SpecialLinearGroup (Fin 2) F,
      u ∈ Work.L2F.hypTorus F d ∧ orderOf u = r ∧
        (u : Matrix (Fin 2) (Fin 2) F).trace = t := by
  have h4ne : (4 : F) ≠ 0 := by
    have h : (4 : F) = 2 * 2 := by norm_num
    rw [h]; exact mul_ne_zero h2 h2
  have h4 : ¬ IsSquare (t * t - 4) := by
    rintro ⟨c, hc⟩
    refine hroot ((t + c) / 2) ?_
    have expand : ((t + c) / 2) ^ 2 - t * ((t + c) / 2) + 1
        = ((t + c) ^ 2 - 2 * t * (t + c) + 4) / 4 := by
      field_simp <;> ring
    have key : (t + c) ^ 2 - 2 * t * (t + c) + 4 = 0 := by linear_combination -hc
    rw [expand, key, zero_div]
  have hdnsq : ¬ IsSquare d := fun h => h.elim (fun a ha => hnsq a ha.symm)
  obtain ⟨c, hc⟩ := SquareMulNonsquare F h2 hdnsq h4
  have ht4 : t * t ≠ 4 := by
    intro h
    have hfac : (t - 2) * (t + 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact rootless_ne_two hroot (by linear_combination h1)
    · exact hroot (-1) (by rw [show t = -2 by linear_combination h1]; ring)
  have hc0 : c ≠ 0 := by
    intro h0
    apply ht4
    have hc' : d * (c * c) = 0 := by rw [h0]; ring
    rw [hc] at hc'
    linear_combination hc'
  have hdet : (t / 2) ^ 2 - d * (c / 2) ^ 2 = 1 := by
    have expand : (t / 2) ^ 2 - d * (c / 2) ^ 2 = (t * t - d * (c * c)) / 4 := by
      field_simp <;> ring
    have key : t * t - d * (c * c) = 4 := by linear_combination -hc
    rw [expand, key, div_self h4ne]
  let u : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨Work.L2F.Mat2.quadMat d (t / 2) (c / 2), by
      rw [Work.L2F.Mat2.quadMat_det]; exact hdet⟩
  have humem : u ∈ Work.L2F.hypTorus F d :=
    (Work.L2F.Conic.mem_hypTorus F d u).mpr ⟨t / 2, c / 2, hdet, rfl⟩
  have htr : (u : Matrix (Fin 2) (Fin 2) F).trace = t := by
    show (Work.L2F.Mat2.quadMat d (t / 2) (c / 2)).trace = t
    rw [Matrix.trace_fin_two]
    simp only [Work.L2F.Mat2.quadMat_apply_00, Work.L2F.Mat2.quadMat_apply_11]
    rw [← two_mul, mul_comm 2 (t / 2)]
    exact div_mul_cancel₀ t h2
  have hpow : u ^ r = 1 := by
    obtain ⟨g, hg⟩ := hdvd
    have hq0 : Polynomial.aeval (u : Matrix (Fin 2) (Fin 2) F) (quad F t) = 0 := by
      rw [show quad F t = quad F ((u : Matrix (Fin 2) (Fin 2) F).trace) by rw [htr],
        aeval_quad_eq_zero u]
    have h1 : Polynomial.aeval (u : Matrix (Fin 2) (Fin 2) F)
        ((Polynomial.X : Polynomial F) ^ r - 1) = 0 := by
      rw [hg, map_mul, hq0, zero_mul]
    rw [aeval_X_pow_sub_one] at h1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    rw [show ((u ^ r : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (u : Matrix (Fin 2) (Fin 2) F) ^ r from rfl]
    exact sub_eq_zero.mp h1
  have hu10 : (u : Matrix (Fin 2) (Fin 2) F) 1 0 = c / 2 := by
    show (Work.L2F.Mat2.quadMat d (t / 2) (c / 2)) 1 0 = c / 2
    rw [Work.L2F.Mat2.quadMat_apply_10]
  have hu1 : u ≠ 1 := by
    intro h
    have h0 : (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [h, Matrix.SpecialLinearGroup.coe_one]
      simp
    rw [hu10] at h0
    exact div_ne_zero hc0 h2 h0
  refine ⟨u, humem, ?_, htr⟩
  have hdvdr : orderOf u ∣ r := orderOf_dvd_iff_pow_eq_one.mpr hpow
  rcases hr.eq_one_or_self_of_dvd (orderOf u) hdvdr with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hu1
  · exact h

/-! ## The fibre of the trace map has two elements -/

theorem trace_eq_or_inv_of_mem_hypTorus {d : F} (h2 : (2 : F) ≠ 0) (hd : d ≠ 0)
    {u w : Matrix.SpecialLinearGroup (Fin 2) F} (hu : u ∈ Work.L2F.hypTorus F d)
    (hw : w ∈ Work.L2F.hypTorus F d)
    (htr : (u : Matrix (Fin 2) (Fin 2) F).trace = (w : Matrix (Fin 2) (Fin 2) F).trace) :
    w = u ∨ w = u⁻¹ := by
  obtain ⟨a, b, hab, hu'⟩ := (Work.L2F.Conic.mem_hypTorus F d u).mp hu
  obtain ⟨a', b', hab', hw'⟩ := (Work.L2F.Conic.mem_hypTorus F d w).mp hw
  have htr2 : a + a = a' + a' := by
    have h1 : (u : Matrix (Fin 2) (Fin 2) F).trace = a + a := by
      rw [hu', Matrix.trace_fin_two]; simp
    have h2' : (w : Matrix (Fin 2) (Fin 2) F).trace = a' + a' := by
      rw [hw', Matrix.trace_fin_two]; simp
    rw [h1, h2'] at htr
    exact htr
  have haa : a = a' := by
    rw [← two_mul, ← two_mul] at htr2
    exact mul_left_cancel₀ h2 htr2
  have hb2 : b ^ 2 = b' ^ 2 := by
    have h : d * b ^ 2 = d * b' ^ 2 := by
      rw [← haa] at hab'
      linear_combination hab' - hab
    exact mul_left_cancel₀ hd h
  have hbb' : b = b' ∨ b' = -b := by
    have h : (b - b') * (b + b') = 0 := by linear_combination hb2
    rcases mul_eq_zero.mp h with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hbb' with hbb | hbb
  · left
    apply Subtype.ext
    rw [hu', hw', haa, hbb]
  · right
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_inv, hu', Matrix.adjugate_fin_two_of, hw', ← haa, hbb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-! ## The main theorem -/

theorem RootlessQuadDvd (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (hnsq : ∃ d : F, d ≠ 0 ∧ ∀ a : F, a * a ≠ d) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    2 * Nat.card {t : F // Work.L2F.Count.Rootless F t ∧
        Work.L2F.Count.quad F t ∣ (Polynomial.X ^ r - 1)}
      = if r ∣ (Nat.card F + 1) then r - 1 else 0 := by
  classical
  obtain ⟨d, hd, hnsq'⟩ := hnsq
  haveI hcyc : IsCyclic (Work.L2F.hypTorus F d) :=
    Work.L2F.Conic.hypTorus_cyclic F h2 d hd
  -- (1) the number of elements of `hypTorus F d` of order `r`
  have hcardH : Nat.card {v : Work.L2F.hypTorus F d // orderOf v = r}
      = if r ∣ (Nat.card F + 1) then r - 1 else 0 := by
    by_cases hdvd : r ∣ Nat.card F + 1
    · rw [if_pos hdvd]
      have hfac : r ∣ Fintype.card (Work.L2F.hypTorus F d) := by
        rw [← Nat.card_eq_fintype_card, Work.L2F.Conic.hypTorus_card F h2 d hd hnsq']
        exact hdvd
      have htot := IsCyclic.card_orderOf_eq_totient (α := Work.L2F.hypTorus F d) hfac
      rw [Nat.totient_prime hr] at htot
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact htot
    · rw [if_neg hdvd, Nat.card_eq_zero]
      refine Or.inl ⟨fun v => ?_⟩
      have hmem : orderOf v.val ∣ Nat.card F + 1 := by
        have h1 : Nat.card (Subgroup.zpowers v.val) ∣ Nat.card (Work.L2F.hypTorus F d) :=
          Subgroup.card_subgroup_dvd_card (Subgroup.zpowers v.val)
        rw [Nat.card_zpowers, Work.L2F.Conic.hypTorus_card F h2 d hd hnsq'] at h1
        exact h1
      rw [v.2] at hmem
      exact hdvd hmem
  -- the two types being compared
  let Stype := {t : F // Rootless F t ∧ quad F t ∣ Polynomial.X ^ r - 1}
  let Ttype := {u : Matrix.SpecialLinearGroup (Fin 2) F //
    u ∈ Work.L2F.hypTorus F d ∧ orderOf u = r}
  -- (2) `Nat.card Ttype = Nat.card {v : hypTorus // orderOf v = r}`
  have hcardT : Nat.card Ttype = if r ∣ (Nat.card F + 1) then r - 1 else 0 := by
    have e : Ttype ≃ {v : Work.L2F.hypTorus F d // orderOf v = r} :=
    { toFun := fun u => ⟨⟨u.1, u.2.1⟩, by rw [Subgroup.orderOf_mk]; exact u.2.2⟩
      invFun := fun v => ⟨v.1.1, ⟨v.1.2, (Subgroup.orderOf_mk v.1.1 v.1.2).symm.trans v.2⟩⟩
      left_inv := fun u => Subtype.ext rfl
      right_inv := fun v => Subtype.ext rfl }
    rw [Nat.card_congr e, hcardH]
  -- the trace map `Ttype → Stype`
  let tr : Ttype → Stype := fun u => ⟨(u.1 : Matrix (Fin 2) (Fin 2) F).trace,
    (rootless_quad_dvd_of_mem_hypTorus hnsq' u.2.1
      (entry10_ne_zero_of_orderOf_eq h2 hr hr2 u.2.1 u.2.2)
      (pow_eq_one_of_orderOf_eq u.2.2)).1,
    (rootless_quad_dvd_of_mem_hypTorus hnsq' u.2.1
      (entry10_ne_zero_of_orderOf_eq h2 hr hr2 u.2.1 u.2.2)
      (pow_eq_one_of_orderOf_eq u.2.2)).2⟩
  -- a chosen preimage of each trace
  have hroot_exists : ∀ s : Stype, ∃ u : Matrix.SpecialLinearGroup (Fin 2) F,
      u ∈ Work.L2F.hypTorus F d ∧ orderOf u = r ∧
        (u : Matrix (Fin 2) (Fin 2) F).trace = s.1 :=
    fun s => exists_hypTorus_orderOf F h2 hd hnsq' hr s.2.1 s.2.2
  let root : Stype → Ttype := fun s =>
    ⟨Classical.choose (hroot_exists s), (Classical.choose_spec (hroot_exists s)).1,
      (Classical.choose_spec (hroot_exists s)).2.1⟩
  have root_trace : ∀ s : Stype, ((root s).1 : Matrix (Fin 2) (Fin 2) F).trace = s.1 :=
    fun s => (Classical.choose_spec (hroot_exists s)).2.2
  have root_mem : ∀ s : Stype, (root s).1 ∈ Work.L2F.hypTorus F d :=
    fun s => (Classical.choose_spec (hroot_exists s)).1
  -- the involution `u ↦ u⁻¹` on `Ttype`
  let tinv : Ttype → Ttype := fun u =>
    ⟨u.1⁻¹, (Work.L2F.hypTorus F d).inv_mem u.2.1, by rw [orderOf_inv]; exact u.2.2⟩
  have tr_root : ∀ s : Stype, tr (root s) = s := by
    intro s
    apply Subtype.ext
    exact root_trace s
  have tr_tinv : ∀ u : Ttype, tr (tinv u) = tr u := by
    intro u
    apply Subtype.ext
    show ((tinv u).1 : Matrix (Fin 2) (Fin 2) F).trace = (u.1 : Matrix (Fin 2) (Fin 2) F).trace
    exact trace_inv_of_mem_hypTorus u.2.1
  have eq_root_or_tinv : ∀ u : Ttype, u = root (tr u) ∨ u = tinv (root (tr u)) := by
    intro u
    have htr : ((root (tr u)).1 : Matrix (Fin 2) (Fin 2) F).trace
        = (u.1 : Matrix (Fin 2) (Fin 2) F).trace := by
      rw [root_trace]
    rcases trace_eq_or_inv_of_mem_hypTorus h2 hd (root_mem (tr u)) u.2.1 htr with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  have root_ne_tinv : ∀ s : Stype, root s ≠ tinv (root s) := by
    intro s hcon
    have hx : (root s).1 = ((root s).1)⁻¹ := by
      have h := congrArg (fun x : Ttype => x.1) hcon
      exact h
    have h2u : (root s).1 ^ 2 = 1 := by
      have h : (root s).1 * (root s).1 = 1 := by
        nth_rewrite 1 [hx]
        rw [inv_mul_cancel]
      simpa [pow_two] using h
    have hdvd2 : orderOf (root s).1 ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2u
    have h2r : r ∣ 2 := by rw [← (root s).2.2]; exact hdvd2
    rcases (Nat.dvd_prime Nat.prime_two).mp h2r with h' | h'
    · exact hr.ne_one h'
    · exact hr2 h'
  -- the bijection `Stype × Fin 2 ≃ Ttype`
  let φ : Stype × Fin 2 → Ttype := fun p => if p.2 = 0 then root p.1 else tinv (root p.1)
  have phi_zero : ∀ s : Stype, φ (s, 0) = root s := by intro s; simp only [φ, if_pos rfl]
  have phi_one : ∀ s : Stype, φ (s, 1) = tinv (root s) := by
    intro s
    simp only [φ, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
  have tr_phi : ∀ (s : Stype) (i : Fin 2), tr (φ (s, i)) = s := by
    intro s i
    rcases fin2_eq_zero_or_eq_one i with rfl | rfl
    · rw [phi_zero]; exact tr_root s
    · rw [phi_one]; exact (tr_tinv (root s)).trans (tr_root s)
  have hinj : Function.Injective φ := by
    rintro ⟨s, i⟩ ⟨s', i'⟩ heq
    have hs : s = s' := by
      have h1 : tr (φ (s, i)) = s := tr_phi s i
      have h2 : tr (φ (s', i')) = s' := tr_phi s' i'
      rw [← h1, heq, h2]
    subst hs
    have hii : i = i' := by
      rcases fin2_eq_zero_or_eq_one i with rfl | rfl <;>
        rcases fin2_eq_zero_or_eq_one i' with rfl | rfl
      · rfl
      · exfalso
        rw [phi_zero, phi_one] at heq
        exact root_ne_tinv s heq
      · exfalso
        rw [phi_zero, phi_one] at heq
        exact root_ne_tinv s heq.symm
      · rfl
    subst hii
    rfl
  have hsurj : Function.Surjective φ := by
    intro u
    rcases eq_root_or_tinv u with h | h
    · exact ⟨(tr u, 0), (phi_zero (tr u)).trans h.symm⟩
    · exact ⟨(tr u, 1), (phi_one (tr u)).trans h.symm⟩
  have hST : Nat.card Ttype = 2 * Nat.card Stype := by
    have e : Stype × Fin 2 ≃ Ttype := Equiv.ofBijective φ ⟨hinj, hsurj⟩
    have h1 : Nat.card Ttype = Nat.card (Stype × Fin 2) := (Nat.card_congr e).symm
    have h2 : Nat.card (Fin 2) = 2 := by simp
    rw [h1, Nat.card_prod, h2, mul_comm]
  show 2 * Nat.card Stype = if r ∣ (Nat.card F + 1) then r - 1 else 0
  rw [← hST, hcardT]

end Work.L2F.Props.Count
