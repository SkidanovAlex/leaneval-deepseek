import Mathlib
import Submission.Work.DSCOH.ShiftToolkit
import Submission.Work.DSCOH.mvpoly_X_pow_mul_left_cancel
import Submission.Work.DSCOH.mvpoly_X_pow_mul_eq_dvd
import Submission.Work.DSCOH.isHomogeneous_eq_zero_of_X_pow_dvd
import Submission.Work.DSCOH.KerDzDefs
import Submission.Work.DSCOH.cechDiff_apply_coe
import Submission.Work.DSCOH.isRegular_of_mem_subS
import Submission.Work.DSCOH.eq_C_mul_X_pow_of_mem_homSub_of_dvd
import Submission.Work.DSCOH.mem_degZero_shift_zero_iff

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-! ## Auxiliary computations -/

/-- The alternating signs attached to the two charts of a two-element index set are opposite, so
they sum to zero. -/
private lemma sum_sign_eq_zero (T : Finset (Fin n)) (hT : T.card = 2) :
    ∑ k ∈ T, ((-1 : ℤ) ^ ((T.filter fun k' => k' < k).card)) = 0 := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hT
  rw [Finset.sum_pair hij]
  rcases lt_or_gt_of_ne hij with h | h
  · have h1 : (({i, j} : Finset (Fin n)).filter fun k => k < i) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨hkmem, hklt⟩ := hk
      rw [Finset.mem_insert, Finset.mem_singleton] at hkmem
      rcases hkmem with hki | hkj
      · exact absurd (hki ▸ hklt) (lt_irrefl i)
      · exact absurd (hkj ▸ hklt) (not_lt.mpr h.le)
    have h2 : (({i, j} : Finset (Fin n)).filter fun k => k < j) = {i} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hki | hkj, hklt⟩
        · exact hki
        · exact absurd (hkj ▸ hklt) (lt_irrefl j)
      · intro hk
        exact ⟨Or.inl hk, hk.symm ▸ h⟩
    rw [h1, h2]
    norm_num
  · have h1 : (({i, j} : Finset (Fin n)).filter fun k => k < i) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hki | hkj, hklt⟩
        · exact absurd (hki ▸ hklt) (lt_irrefl i)
        · exact hkj
      · intro hk
        exact ⟨Or.inr hk, hk.symm ▸ h⟩
    have h2 : (({i, j} : Finset (Fin n)).filter fun k => k < j) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨hkmem, hklt⟩ := hk
      rw [Finset.mem_insert, Finset.mem_singleton] at hkmem
      rcases hkmem with hki | hkj
      · exact absurd (hki ▸ hklt) (not_lt.mpr h.le)
      · exact absurd (hkj ▸ hklt) (lt_irrefl j)
    rw [h1, h2]
    norm_num

/-- **The constant cochain is a cocycle.**  On a two-element index the differential is the
alternating sum of two terms which are both the image of the same constant in the chart `{i,j}`
(naturality of the restriction maps on the classes of the structure map, `Work.DSCOH.resAt_toLoc`),
and the two signs cancel (`Work.DSCOH.sum_sign_eq_zero`). -/
private theorem cechDiff_zero_constLin
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) 0)] (a : A) :
    cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) 0) 0
      (constLin (A := A) (n := n) a) = 0 := by
  funext T
  refine Subtype.ext ?_
  rw [cechDiff_apply_coe]
  have hsum : (∑ l ∈ T.1.attach, ((-1 : ℤ) ^ ((T.1.filter fun k => k < l.1).card)) •
        resAt (A := A) (M := Poly A n) (Finset.erase_subset l.1 T.1)
          ↑((constLin (A := A) (n := n) a)
            ⟨T.1.erase l.1, by rw [Finset.card_erase_of_mem l.2]; omega⟩))
      = ∑ l ∈ T.1.attach, ((-1 : ℤ) ^ ((T.1.filter fun k => k < l.1).card)) •
        toLoc (A := A) (M := Poly A n) T.1 (MvPolynomial.C a) := by
    apply Finset.sum_congr rfl
    intro l _
    rw [constLin_apply (A := A) (n := n) a
      ⟨T.1.erase l.1, by rw [Finset.card_erase_of_mem l.2]; omega⟩]
    congr 1
    exact resAt_toLoc (A := A) (n := n) (T.1.erase l.1) T.1 (Finset.erase_subset l.1 T.1)
      (MvPolynomial.C a)
  have hcongr : (∑ i ∈ (T.1).attach, ((-1 : ℤ) ^ ((T.1.filter fun k => k < i.1).card)))
      = ∑ i ∈ (T.1).attach,
        (fun k : Fin n => ((-1 : ℤ) ^ ((T.1.filter fun k' => k' < k).card))) i.1 :=
    Finset.sum_congr rfl fun i _ => rfl
  have hsum2 := Finset.sum_attach (s := T.1)
    (f := fun k : Fin n => ((-1 : ℤ) ^ ((T.1.filter fun k' => k' < k).card)))
  rw [hsum, ← Finset.sum_smul, hcongr, hsum2, sum_sign_eq_zero T.1 T.2, zero_smul]
  rfl

/-- Equal elements of a subtype have `HEq`-related images under any dependent function. -/
lemma heq_apply {α : Sort*} {β : α → Sort*} {a b : α} (h : a = b) (f : (x : α) → β x) :
    HEq (f a) (f b) := by
  subst h
  rfl

/-- The chart restriction maps are compatible with the identification of the localizations at
charts which are equal as finsets: the elements of two equal charts are identified by the
corresponding `cast`, and the restriction maps to a common chart commute with it. -/
lemma resAt_heq_degZero {ℳ : ℕ → Submodule A (Poly A n)} [SetLike.GradedSMul (homSub A n) ℳ]
    {S S' T : Finset (Fin n)} (hS : S = S') (h₁ : S ⊆ T) (h₂ : S' ⊆ T)
    {x : degZero (A := A) ℳ S} {y : degZero (A := A) ℳ S'} (hxy : HEq x y) :
    resAt (A := A) (M := Poly A n) h₁ x.1 = resAt (A := A) (M := Poly A n) h₂ y.1 := by
  subst hS
  rw [eq_of_heq hxy]

/-- **The two components of a `0`-cocycle of the chart Čech complex on a pair of charts agree on
the overlap.**  Evaluating the vanishing of the differential at the `2`-element index `{i,j}` and
computing the alternating sum of the two terms (`Work.DSCOH.cechDiff_apply_coe`) gives the
relation, since the two signs are opposite and the erased charts `{i,j} \ {i} = {j}` and
`{i,j} \ {j} = {i}` are the two singleton charts. -/
private theorem resAt_eq_of_cechDiff_zero_stub (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    {i j : Fin n} (hij : i ≠ j)
    (c : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0)
    (hc : cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0 c = 0) :
    resAt (A := A) (M := Poly A n) (S := {j}) (T := {i, j}) (by simp)
        (c ⟨{j}, Finset.card_singleton j⟩)
      = resAt (A := A) (M := Poly A n) (S := {i}) (T := {i, j}) (by simp)
        (c ⟨{i}, Finset.card_singleton i⟩) := by
  have hcard : ({i, j} : Finset (Fin n)).card = 0 + 1 + 1 := by
    rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
  have hcomp : (((cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0) c
      ⟨({i, j} : Finset (Fin n)), hcard⟩ : degZero (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) {i, j}) : locAt (A := A) (M := Poly A n) {i, j}) = 0 := by
    rw [congr_fun hc ⟨({i, j} : Finset (Fin n)), hcard⟩]
    rfl
  rw [cechDiff_apply_coe] at hcomp
  simp only [Subtype.coe_mk] at hcomp
  set F : Fin n → locAt (A := A) (M := Poly A n) {i, j} := fun k =>
    if h : k ∈ ({i, j} : Finset (Fin n)) then
      ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k' => k' < k).card)) •
        resAt (A := A) (M := Poly A n) (Finset.erase_subset k {i, j})
          ((c ⟨({i, j} : Finset (Fin n)).erase k,
            by rw [Finset.card_erase_of_mem h]; omega⟩ :
            degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
              (({i, j} : Finset (Fin n)).erase k)).1)
    else 0 with hF
  have hsumF : ∑ k ∈ ({i, j} : Finset (Fin n)), F k = 0 := by
    rw [← Finset.sum_attach (s := ({i, j} : Finset (Fin n))) (f := F)]
    rw [← hcomp]
    apply Finset.sum_congr rfl
    intro l _
    rw [hF]
    dsimp only
    rw [dif_pos l.2]
  rw [Finset.sum_pair hij] at hsumF
  -- identification of the two erased charts with the singletons
  have hErase_i : ({i, j} : Finset (Fin n)).erase i = {j} :=
    Finset.erase_insert (by simpa using hij)
  have hErase_j : ({i, j} : Finset (Fin n)).erase j = {i} := by
    rw [Finset.pair_comm]
    exact Finset.erase_insert (by simpa using hij.symm)
  have hFi : F i = ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < i).card)) •
      resAt (A := A) (M := Poly A n) (by simp : ({j} : Finset (Fin n)) ⊆ {i, j})
        (c ⟨{j}, Finset.card_singleton j⟩) := by
    rw [hF]
    dsimp only
    rw [dif_pos (Finset.mem_insert_self i {j})]
    congr 1
    exact resAt_heq_degZero (S := ({i, j} : Finset (Fin n)).erase i) (S' := {j})
      (T := ({i, j} : Finset (Fin n))) hErase_i (Finset.erase_subset i {i, j}) (by simp)
      (x := c ⟨({i, j} : Finset (Fin n)).erase i,
        by rw [hErase_i]; exact Finset.card_singleton j⟩)
      (y := c ⟨{j}, Finset.card_singleton j⟩)
      (heq_apply (Subtype.ext hErase_i) c)
  have hFj : F j = ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < j).card)) •
      resAt (A := A) (M := Poly A n) (by simp : ({i} : Finset (Fin n)) ⊆ {i, j})
        (c ⟨{i}, Finset.card_singleton i⟩) := by
    rw [hF]
    dsimp only
    rw [dif_pos (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))]
    congr 1
    exact resAt_heq_degZero (S := ({i, j} : Finset (Fin n)).erase j) (S' := {i})
      (T := ({i, j} : Finset (Fin n))) hErase_j (Finset.erase_subset j {i, j}) (by simp)
      (x := c ⟨({i, j} : Finset (Fin n)).erase j,
        by rw [hErase_j]; exact Finset.card_singleton i⟩)
      (y := c ⟨{i}, Finset.card_singleton i⟩)
      (heq_apply (Subtype.ext hErase_j) c)
  rw [hFi, hFj] at hsumF
  -- the two signs are opposite
  have hsign : ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < i).card)) +
      ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < j).card)) = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · have h1 : (({i, j} : Finset (Fin n)).filter fun k => k < i) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k hk
        rw [Finset.mem_filter] at hk
        obtain ⟨hkmem, hklt⟩ := hk
        rw [Finset.mem_insert, Finset.mem_singleton] at hkmem
        rcases hkmem with hki | hkj
        · exact absurd (hki ▸ hklt) (lt_irrefl i)
        · exact absurd (hkj ▸ hklt) (not_lt.mpr h.le)
      have h2 : (({i, j} : Finset (Fin n)).filter fun k => k < j) = {i} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hki | hkj, hklt⟩
          · exact hki
          · exact absurd (hkj ▸ hklt) (lt_irrefl j)
        · intro hk
          exact ⟨Or.inl hk, hk.symm ▸ h⟩
      rw [h1, h2]
      norm_num
    · have h1 : (({i, j} : Finset (Fin n)).filter fun k => k < i) = {j} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hki | hkj, hklt⟩
          · exact absurd (hki ▸ hklt) (lt_irrefl i)
          · exact hkj
        · intro hk
          exact ⟨Or.inr hk, hk.symm ▸ h⟩
      have h2 : (({i, j} : Finset (Fin n)).filter fun k => k < j) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k hk
        rw [Finset.mem_filter] at hk
        obtain ⟨hkmem, hklt⟩ := hk
        rw [Finset.mem_insert, Finset.mem_singleton] at hkmem
        rcases hkmem with hki | hkj
        · exact absurd (hki ▸ hklt) (not_lt.mpr h.le)
        · exact absurd (hkj ▸ hklt) (lt_irrefl j)
      rw [h1, h2]
      norm_num
  have hs : ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < j).card)) =
      -((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < i).card)) := by
    linarith [hsign]
  have hs1 : ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < i).card)) = 1 ∨
      ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < i).card)) = -1 := by
    rcases Nat.even_or_odd ((({i, j} : Finset (Fin n)).filter fun k => k < i).card) with he | ho
    · exact Or.inl he.neg_one_pow
    · exact Or.inr ho.neg_one_pow
  rcases hs1 with hone | hone
  · have hneg : ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < j).card)) = -1 := by
      rw [hs, hone]
    rw [hone, hneg, one_smul, neg_one_smul] at hsumF
    exact sub_eq_zero.mp hsumF
  · have hneg : ((-1 : ℤ) ^ ((({i, j} : Finset (Fin n)).filter fun k => k < j).card)) = 1 := by
      rw [hs, hone]
      ring
    rw [hone, hneg, neg_one_smul, one_smul] at hsumF
    exact neg_add_eq_zero.mp hsumF

/-! ## The main argument -/

/-- The structure maps of the chart localizations only depend on the subsets, not on the proof
of the inclusion. -/
lemma resAt_congr {S T : Finset (Fin n)} {h₁ h₂ : S ⊆ T} :
    resAt (A := A) (M := Poly A n) h₁ = resAt (A := A) (M := Poly A n) h₂ := by
  show LocalizedModule.liftOfLE (subS (A := A) S) (subS (A := A) T) (subS_mono (A := A) h₁) =
    LocalizedModule.liftOfLE (subS (A := A) S) (subS (A := A) T) (subS_mono (A := A) h₂)
  rw [Subsingleton.elim (subS_mono (A := A) h₁) (subS_mono (A := A) h₂)]

/-- **The two components of a Čech `0`-cocycle in the charts `{i}` and `{j}` are the same
constant.**  An element of the degree-zero part of the localization at `{i}` which agrees with
an element of the degree-zero part of the localization at `{j}` in the common chart `{i,j}`
must be a constant (`a/1`), and both are then the same constant. -/
theorem eq_const_of_resAt_eq [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) 0)]
    {i j : Fin n} (hij : i ≠ j)
    (x : degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) 0)
      ({i} : Finset (Fin n)))
    (y : degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) 0)
      ({j} : Finset (Fin n)))
    {h₁ : ({i} : Finset (Fin n)) ⊆ {i, j}} {h₂ : ({j} : Finset (Fin n)) ⊆ {i, j}}
    (h : resAt (A := A) (M := Poly A n) h₁ x.1 = resAt (A := A) (M := Poly A n) h₂ y.1) :
    ∃ a : A, x.1 = toLoc (A := A) (M := Poly A n) {i} (MvPolynomial.C a) ∧
      y.1 = toLoc (A := A) (M := Poly A n) {j} (MvPolynomial.C a) := by
  obtain ⟨k, m, hm, hx⟩ :=
    (mem_degZero_shift_zero_iff (A := A) (n := n) ({i} : Finset (Fin n)) x.1).mp x.2
  obtain ⟨l, g, hg, hy⟩ :=
    (mem_degZero_shift_zero_iff (A := A) (n := n) ({j} : Finset (Fin n)) y.1).mp y.2
  have hm' : m ∈ homSub A n k := by simpa using hm
  -- the two fractions are equal in the common chart `{i,j}`
  rw [← hx, ← hy, divPow_toLoc_eq_mk (A := A) (n := n) {i} k m,
    divPow_toLoc_eq_mk (A := A) (n := n) {j} l g,
    resAt_mk (A := A) {i} {i, j} h₁ m (den (A := A) {i} k),
    resAt_mk (A := A) {j} {i, j} h₂ g (den (A := A) {j} l)] at h
  simp only [den_coe, monomial_singleton (A := A) (n := n) i,
    monomial_singleton (A := A) (n := n) j] at h
  -- cancel the common factor `u` (a product of variables, hence a non-zero-divisor)
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h
  simp only [Submonoid.smul_def] at hu
  have hreg : IsRegular (↑u : Poly A n) := isRegular_of_mem_subS u.2
  have hkey : (MvPolynomial.X j : Poly A n) ^ l * m =
      (MvPolynomial.X i : Poly A n) ^ k * g := hreg.left hu
  -- `X i ^ k` divides `m`, and `m` is homogeneous of degree `k`, so `m = C a * X i ^ k`
  have hdvd : (MvPolynomial.X i : Poly A n) ^ k ∣ m :=
    mvpoly_X_pow_mul_eq_dvd (A := A) (i := j) (j := i) hij.symm hkey
  obtain ⟨a, ha⟩ := eq_C_mul_X_pow_of_mem_homSub_of_dvd hm' hdvd
  refine ⟨a, ?_, ?_⟩
  · rw [← hx, ha, divPow_toLoc_eq_mk (A := A) (n := n) {i} k
      (MvPolynomial.C a * (MvPolynomial.X i : Poly A n) ^ k)]
    show LocalizedModule.mk (MvPolynomial.C a * (MvPolynomial.X i : Poly A n) ^ k)
        (den (A := A) {i} k) =
      LocalizedModule.mk (MvPolynomial.C a) 1
    rw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_one, den_coe,
      monomial_singleton (A := A) (n := n) i]
    ring
  · have hg'' : g = (MvPolynomial.X j : Poly A n) ^ l * MvPolynomial.C a := by
      have h2 : (MvPolynomial.X i : Poly A n) ^ k * g =
          (MvPolynomial.X i : Poly A n) ^ k *
            ((MvPolynomial.X j : Poly A n) ^ l * MvPolynomial.C a) := by
        rw [← hkey, ha]
        ring
      exact (MvPolynomial.isRegular_X_pow (R := A) (n := i) k).left h2
    rw [← hy, hg'', divPow_toLoc_eq_mk (A := A) (n := n) {j} l
      ((MvPolynomial.X j : Poly A n) ^ l * MvPolynomial.C a)]
    show LocalizedModule.mk ((MvPolynomial.X j : Poly A n) ^ l * MvPolynomial.C a)
        (den (A := A) {j} l) =
      LocalizedModule.mk (MvPolynomial.C a) 1
    rw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_one, den_coe,
      monomial_singleton (A := A) (n := n) j]
    ring

/-- A Čech `0`-cochain is determined by its values on the singleton charts. -/
lemma eq_of_eq_singletons {c c' : CechTerm (A := A) (n := n) (M := Poly A n)
    (shift (A := A) (n := n) 0) 0}
    (h : ∀ (i : Fin n) (hi : ({i} : Finset (Fin n)).card = 0 + 1),
      c ⟨{i}, hi⟩ = c' ⟨{i}, hi⟩) : c = c' := by
  funext T
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp T.2
  have hsub : T = ⟨({x} : Finset (Fin n)), by rw [← hx]; exact T.2⟩ := Subtype.ext hx
  rw [hsub]
  exact h x (by rw [← hx]; exact T.2)

/-- **Every `0`-cocycle of the chart Čech complex of the standard grading is a constant
family**: its value on the chart `{i}` is the class of a fixed constant `a : A`. -/
theorem const_of_mem_ker [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) 0)]
    (hn : 2 ≤ n)
    (c : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) 0) 0)
    (hc : cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) 0) 0 c = 0) :
    ∃ a : A, ∀ (i : Fin n) (hi : ({i} : Finset (Fin n)).card = 0 + 1),
      c ⟨{i}, hi⟩ = constElem (A := A) (n := n) ({i} : Finset (Fin n)) a := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have h2 : (i0 : ℕ) = (i1 : ℕ) := congrArg Fin.val h
    simp [i0, i1] at h2
  have hrel : resAt (A := A) (M := Poly A n)
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i0 {i1}))
        (c ⟨{i0}, Finset.card_singleton i0⟩).1 =
      resAt (A := A) (M := Poly A n)
        (Finset.singleton_subset_iff.mpr
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self i1)))
        (c ⟨{i1}, Finset.card_singleton i1⟩).1 :=
    (resAt_eq_of_cechDiff_zero_stub (A := A) (n := n) 0 hi01 c hc).symm
  obtain ⟨a, ha0, -⟩ := eq_const_of_resAt_eq (A := A) (n := n) hi01 _ _ hrel
  refine ⟨a, fun i hi => ?_⟩
  by_cases hi0 : i = i0
  · subst hi0
    exact Subtype.ext ha0
  · have hrel' : resAt (A := A) (M := Poly A n)
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {i0}))
          (c ⟨{i}, Finset.card_singleton i⟩).1 =
        resAt (A := A) (M := Poly A n)
          (Finset.singleton_subset_iff.mpr
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self i0)))
          (c ⟨{i0}, Finset.card_singleton i0⟩).1 :=
      (resAt_eq_of_cechDiff_zero_stub (A := A) (n := n) 0 hi0 c hc).symm
    obtain ⟨b, hb, hb0⟩ := eq_const_of_resAt_eq (A := A) (n := n) hi0 _ _ hrel'
    have hba : b = a := by
      have hh : toLoc (A := A) (M := Poly A n) {i0} (MvPolynomial.C b) =
          toLoc (A := A) (M := Poly A n) {i0} (MvPolynomial.C a) := by
        rw [← hb0, ha0]
      have hh' : LocalizedModule.mk (MvPolynomial.C b) 1 =
          LocalizedModule.mk (MvPolynomial.C a) 1 := hh
      obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hh'
      simp only [Submonoid.smul_def] at hu
      have hreg : IsRegular (↑u : Poly A n) := isRegular_of_mem_subS u.2
      have h2 : (MvPolynomial.C b : Poly A n) = MvPolynomial.C a := by
        simpa using hreg.left hu
      exact (MvPolynomial.C_injective (Fin n) (R := A)) h2
    subst hba
    exact Subtype.ext hb

/-- The `A`-linear map `A → ker (cechDiff 0)` sending `a` to the constant family. -/
noncomputable def toKer [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) 0)] :
    A →ₗ[A] LinearMap.ker (cechDiff (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) 0) 0) :=
  (constLin (A := A) (n := n)).codRestrict _ fun a => by
    rw [LinearMap.mem_ker]
    exact cechDiff_zero_constLin (A := A) (n := n) a

theorem ker_cechDiff_zero_finite_dzero {A : Type*} [CommRing A] {n : ℕ} (hn : 2 ≤ n)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) 0)] :
    Module.Finite A (LinearMap.ker (cechDiff (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) 0) 0)) := by
  have hsurj : Function.Surjective (toKer (A := A) (n := n)) := by
    intro c
    obtain ⟨a, ha⟩ := const_of_mem_ker (A := A) (n := n) hn c.1 c.2
    refine ⟨a, ?_⟩
    refine Subtype.ext ?_
    refine eq_of_eq_singletons (A := A) (n := n) fun i hi => ?_
    change constLin (A := A) (n := n) a ⟨{i}, hi⟩ = c.1 ⟨{i}, hi⟩
    rw [constLin_apply (A := A) (n := n) a ⟨{i}, hi⟩]
    exact (ha i hi).symm
  exact Module.Finite.of_surjective (toKer (A := A) (n := n)) hsurj

end Work.DSCOH
