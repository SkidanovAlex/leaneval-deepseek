import Mathlib
import Submission.Commons.Combinatorics.MvPolynomial.interval_convex_of_rayleigh
import Submission.Commons.LorentzianPolynomials.strict_subset_L

namespace Commons.Combinatorics.MvPolynomial

open Finsupp
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section



/-- subtracting then adding back the same unit vector is the identity when the coordinate is ≥ 1 -/
lemma sub_single_add_self {n : ℕ} (m : Fin n →₀ ℕ) (i : Fin n) (hi : 1 ≤ m i) :
    (m - e i) + e i = m := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [e]
    omega
  · have hz : (e i) k = 0 := Finsupp.single_eq_of_ne (a := i) (b := (1 : ℕ)) (a' := k) (by simpa using hki)
    simp [e, hz]

/-- roundtrip: (m - e i + e j) + e i - e j = m when i ≠ j and m i ≥ 1 -/
lemma shift_then_unshift {n : ℕ} (m : Fin n →₀ ℕ) (i j : Fin n) (hij : i ≠ j) (hmi : 1 ≤ m i) :
    (m - e i + e j) + e i - e j = m := by
  calc
    (((m - e i) + e j) + e i) - e j = (((m - e i) + e i) + e j) - e j := by
      rw [add_assoc (m - e i) (e j) (e i), add_comm (e j) (e i), ← add_assoc (m - e i) (e i) (e j)]
    _ = (m + e j) - e j := by rw [sub_single_add_self m i hmi]
    _ = m := by rw [add_sub_single m j]

/-- (m + e i - e j) - e i + e j = m when i ≠ j and m j ≥ 1 -/
lemma unshift_then_shift {n : ℕ} (m : Fin n →₀ ℕ) (i j : Fin n) (hij : i ≠ j) (hmj : 1 ≤ m j) :
    (m + e i - e j) - e i + e j = m := by
  calc
    (((m + e i) - e j) - e i) + e j = (((m + e i) - e i) - e j) + e j := by
      rw [sub_sub_comm (m + e i) j i]
    _ = (m - e j) + e j := by rw [add_sub_single m i]
    _ = m := by rw [sub_single_add_self m j hmj]

/-- (x - e k + e i) - e i + e j = x - e k + e j -/
lemma move_i_then_shift {n : ℕ} (x : Fin n →₀ ℕ) (i j k : Fin n) :
    (x - e k + e i) - e i + e j = x - e k + e j := by
  calc
    (((x - e k) + e i) - e i) + e j = (x - e k) + e j := by rw [add_sub_single (x - e k) i]
    _ = x - e k + e j := rfl

/-- (x - e k + e j) - e j + e i = x - e k + e i -/
lemma move_j_then_unshift {n : ℕ} (x : Fin n →₀ ℕ) (i j k : Fin n) :
    (x - e k + e j) - e j + e i = x - e k + e i := by
  calc
    (((x - e k) + e j) - e j) + e i = (x - e k) + e i := by rw [add_sub_single (x - e k) j]
    _ = x - e k + e i := rfl

/-- (a + e i) - e j = (a - e j) + e i when i ≠ j -/
lemma add_sub_swap {n : ℕ} (a : Fin n →₀ ℕ) (i j : Fin n) (hij : i ≠ j) :
    (a + e i) - e j = (a - e j) + e i := by
  ext k
  by_cases hkj : k = j
  · subst k
    have hz : (e i) j = 0 := Finsupp.single_eq_of_ne (a := i) (b := (1 : ℕ)) (a' := j) hij.symm
    simp [e, hz]
  · by_cases hki : k = i
    · subst k
      have hz : (e j) i = 0 := Finsupp.single_eq_of_ne (a := j) (b := (1 : ℕ)) (a' := i) hij
      simp [e, hz]
    · have hzi : (e i) k = 0 := Finsupp.single_eq_of_ne (a := i) (b := (1 : ℕ)) (a' := k) (by simpa using hki)
      have hzj : (e j) k = 0 := Finsupp.single_eq_of_ne (a := j) (b := (1 : ℕ)) (a' := k) (by simpa using hkj)
      simp [e, hzi, hzj]

/-- (x - e j) + e l = (x + e l) - e j when l ≠ j -/
lemma add_sub_shift {n : ℕ} (x : Fin n →₀ ℕ) (j l : Fin n) (hlj : l ≠ j) :
    (x - e j) + e l = (x + e l) - e j := by
  ext k
  by_cases hkj : k = j
  · subst k
    have hz : (e l) j = 0 := Finsupp.single_eq_of_ne (a := l) (b := (1 : ℕ)) (a' := j) hlj.symm
    simp [e, hz]
  · by_cases hkl : k = l
    · subst k
      have hz : (e j) l = 0 := Finsupp.single_eq_of_ne (a := j) (b := (1 : ℕ)) (a' := l) hlj
      simp [e, hz]
    · have hzj : (e j) k = 0 := Finsupp.single_eq_of_ne (a := j) (b := (1 : ℕ)) (a' := k) (by simpa using hkj)
      have hzl : (e l) k = 0 := Finsupp.single_eq_of_ne (a := l) (b := (1 : ℕ)) (a' := k) (by simpa using hkl)
      simp [e, hzj, hzl]

/-- the shifted set: m with m i ≥ 1 and m - e i + e j ∈ A -/
abbrev shiftSet {n : ℕ} (A : Set (Fin n →₀ ℕ)) (i j : Fin n) : Set (Fin n →₀ ℕ) :=
  {m : Fin n →₀ ℕ | m i ≥ 1 ∧ m - e i + e j ∈ A}

/-- membership in the shifted set gives the roundtrip representation -/
lemma shiftSet_eq_source_add {n : ℕ} (A : Set (Fin n →₀ ℕ)) (i j : Fin n) (hij : i ≠ j)
    {β : Fin n →₀ ℕ} (hβ : β ∈ shiftSet A i j) :
    β = (β - e i + e j) + e i - e j := by
  exact (shift_then_unshift β i j hij hβ.1).symm

/-- source of a shifted element is in A -/
lemma shiftSet_source_mem {n : ℕ} (A : Set (Fin n →₀ ℕ)) (i j : Fin n)
    {β : Fin n →₀ ℕ} (hβ : β ∈ shiftSet A i j) : β - e i + e j ∈ A := hβ.2

/-- coordinate i of a shifted element is positive -/
lemma shiftSet_i_pos {n : ℕ} (A : Set (Fin n →₀ ℕ)) (i j : Fin n)
    {β : Fin n →₀ ℕ} (hβ : β ∈ shiftSet A i j) : 1 ≤ β i := hβ.1
/-- when `i = j` the shifted set is contained in `A` -/
lemma shiftSet_self_subset {n : ℕ} (A : Set (Fin n →₀ ℕ)) (i : Fin n) :
    shiftSet A i i ⊆ A := by
  intro m hm
  have hmm : m - e i + e i = m := sub_single_add_self m i hm.1
  simpa [hmm] using hm.2

/-- coordinate i of (m - e i + e j) -/
lemma sub_add_apply_j {n : ℕ} (m : Fin n →₀ ℕ) (i j : Fin n) (hij : i ≠ j) :
    (m - e i + e j) j = m j + 1 := by
  have hz : (e i) j = 0 := Finsupp.single_eq_of_ne (a := i) (b := (1 : ℕ)) (a' := j) hij.symm
  simp [e, hz]

/-- (m + e i - e j) i = m i + 1 -/
lemma unshift_i {n : ℕ} (m : Fin n →₀ ℕ) (i j : Fin n) (hij : i ≠ j) :
    (m + e i - e j) i = m i + 1 := by
  have hz : (e j) i = 0 := Finsupp.single_eq_of_ne (a := j) (b := (1 : ℕ)) (a' := i) hij
  simp [e, hz]

/-- (m + e i - e j) j = m j - 1, when m j ≥ 1 -/
lemma unshift_j {n : ℕ} (m : Fin n →₀ ℕ) (i j : Fin n) (hij : i ≠ j) (hmj : 1 ≤ m j) :
    (m + e i - e j) j = m j - 1 := by
  have hz : (e i) j = 0 := Finsupp.single_eq_of_ne (a := i) (b := (1 : ℕ)) (a' := j) hij.symm
  simp [e, hz]

/-- (m + e i - e j) k = m k when k ≠ i, j -/
lemma unshift_o {n : ℕ} (m : Fin n →₀ ℕ) (i j k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
    (m + e i - e j) k = m k := by
  have hzi : (e i) k = 0 := Finsupp.single_eq_of_ne (a := i) (b := (1 : ℕ)) (a' := k) (by simpa using hki)
  have hzj : (e j) k = 0 := Finsupp.single_eq_of_ne (a := j) (b := (1 : ℕ)) (a' := k) (by simpa using hkj)
  simp [e, hzi, hzj]

/-- Φ(T(a) − e_k + e_l) = a − e_k + e_l, when k ∉ {i, j}: needs only a_j ≥ 1 -/
lemma shift_move_out {n : ℕ} (a : Fin n →₀ ℕ) (i j k l : Fin n)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (haj : 1 ≤ a j) :
    (a + e i - e j) - e k + e l - e i + e j = a - e k + e l := by
  ext t
  by_cases hli : l = i <;> by_cases hlj : l = j
  all_goals
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htk : t = k <;> by_cases htl : t = l
    all_goals simp_all [e, Finsupp.single_apply]
    all_goals omega

/-- k = i case: needs a_i ≥ 1 and a_j ≥ 1 -/
lemma shift_move_ki {n : ℕ} (a : Fin n →₀ ℕ) (i j l : Fin n)
    (hij : i ≠ j) (hai : 1 ≤ a i) (haj : 1 ≤ a j) :
    (a + e i - e j) - e i + e l - e i + e j = a - e i + e l := by
  ext t
  by_cases hli : l = i <;> by_cases hlj : l = j
  all_goals
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l
    all_goals simp_all [e, Finsupp.single_apply]
    all_goals omega

/-- k = j case: needs a_j ≥ 2 -/
lemma shift_move_kj {n : ℕ} (a : Fin n →₀ ℕ) (i j l : Fin n)
    (hij : i ≠ j) (haj : 2 ≤ a j) :
    (a + e i - e j) - e j + e l - e i + e j = a - e j + e l := by
  ext t
  by_cases hli : l = i <;> by_cases hlj : l = j
  all_goals
    by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l
    all_goals simp_all [e, Finsupp.single_apply]
    all_goals omega



/-- Case: both `α` and `β` lie in the shifted set.  Unshifting both sides reduces to an
exchange inside `A`; the exchange lifts back to the shifted set. -/
lemma union_exch_SS {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i ≠ j)
    {α β : Fin n →₀ ℕ} (k : Fin n) (hαS : α ∈ shiftSet A i j) (hβS : β ∈ shiftSet A i j)
    (hgt : α k > β k) :
    ∃ l : Fin n, α l < β l ∧ α - e k + e l ∈ A ∪ shiftSet A i j := by
  let a : Fin n →₀ ℕ := α - e i + e j
  let b : Fin n →₀ ℕ := β - e i + e j
  have haA : a ∈ A := by simpa [a] using hαS.2
  have hbA : b ∈ A := by simpa [b] using hβS.2
  have hαe : α = a + e i - e j := by
    simpa [a] using (shift_then_unshift α i j hij hαS.1).symm
  have hβe : β = b + e i - e j := by
    simpa [b] using (shift_then_unshift β i j hij hβS.1).symm
  have haj : 1 ≤ a j := by
    have hc : a j = α j + 1 := by
      simpa [a] using (sub_add_apply_j α i j hij)
    omega
  have hbj : 1 ≤ b j := by
    have hc : b j = β j + 1 := by simpa [b] using (sub_add_apply_j β i j hij)
    omega
  -- α k > β k  ⟺  a k > b k
  have hgtA : a k > b k := by
    by_cases hki : k = i
    · subst k
      have hαi : α i = a i + 1 := by rw [hαe, unshift_i a i j hij]
      have hβi : β i = b i + 1 := by rw [hβe, unshift_i b i j hij]
      omega
    · by_cases hkj : k = j
      · subst k
        have hαj : α j = a j - 1 := by rw [hαe, unshift_j a i j hij haj]
        have hβj : β j = b j - 1 := by rw [hβe, unshift_j b i j hij hbj]
        omega
      · have hαk : α k = a k := by rw [hαe, unshift_o a i j k hki hkj]
        have hβk : β k = b k := by rw [hβe, unshift_o b i j k hki hkj]
        omega
  rcases hA a haA b hbA k hgtA with ⟨l, hltA, hmA⟩
  refine ⟨l, ?_, ?_⟩
  · -- α l < β l
    by_cases hli : l = i
    · subst l
      have hαi : α i = a i + 1 := by rw [hαe, unshift_i a i j hij]
      have hβi : β i = b i + 1 := by rw [hβe, unshift_i b i j hij]
      omega
    · by_cases hlj : l = j
      · subst l
        have hαj : α j = a j - 1 := by rw [hαe, unshift_j a i j hij haj]
        have hβj : β j = b j - 1 := by rw [hβe, unshift_j b i j hij hbj]
        omega
      · have hαl : α l = a l := by rw [hαe, unshift_o a i j l hli hlj]
        have hβl : β l = b l := by rw [hβe, unshift_o b i j l hli hlj]
        omega
  · -- γ := α - e k + e l belongs to A ∪ shiftSet
    let γ : Fin n →₀ ℕ := α - e k + e l
    by_cases hlk : l = k
    · -- γ = α (subtract and re-add at the same coordinate k, exact since α k ≥ 1)
      subst l
      have hαk1 : 1 ≤ α k := by omega
      rw [sub_single_add_self α k hαk1]
      exact Or.inr hαS
    · -- otherwise γ ∈ shiftSet via the shift-commutation Φ(γ) = a - e k + e l ∈ A
      have hγphi : γ - e i + e j = a - e k + e l := by
        subst γ
        rw [hαe]
        by_cases hki : k = i
        · subst k
          have hai : 1 ≤ a i := by omega
          exact shift_move_ki a i j l hij hai haj
        · by_cases hkj : k = j
          · subst k
            have haj2 : 2 ≤ a j := by
              have : a j > b j := by simpa using hgtA
              omega
            exact shift_move_kj a i j l hij haj2
          · exact shift_move_out a i j k l hij hki hkj haj
      have hγS : γ ∈ shiftSet A i j := by
        constructor
        · -- γ i ≥ 1
          subst γ
          rw [hαe]
          simp_all [e, Finsupp.single_apply, hij]
          by_cases hli : l = i <;> by_cases hki : k = i
          all_goals simp_all [e, Finsupp.single_apply, hij]
          all_goals omega
        · -- Φ γ ∈ A
          have : γ - e i + e j ∈ A := by
            rw [hγphi]
            exact hmA
          simpa [γ] using this
      exact Or.inr hγS



/-- (x - e j + e i) - e i + e j = x, when x j ≥ 1 -/
lemma move_j_i_roundtrip {n : ℕ} (x : Fin n →₀ ℕ) (i j : Fin n) (hij : i ≠ j) (hxj : 1 ≤ x j) :
    (x - e j + e i) - e i + e j = x := by
  calc
    (((x - e j) + e i) - e i) + e j = (x - e j) + e j := by rw [add_sub_single (x - e j) i]
    _ = x := by rw [sub_single_add_self x j hxj]

/-- (x - e j + e o) - e i + e j = x - e i + e o for o ∉ {i,j}, x j ≥ 1 -/
lemma move_j_o_phi {n : ℕ} (x : Fin n →₀ ℕ) (i j o : Fin n) (hij : i ≠ j)
    (hoi : o ≠ i) (hoj : o ≠ j) (hxj : 1 ≤ x j) :
    (x - e j + e o) - e i + e j = x - e i + e o := by
  ext t
  by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases hto : t = o
  all_goals simp_all [e, Finsupp.single_apply]
  all_goals omega

/-- (x - e k + e o) - e i + e j = (x - e k + e j) - e i + e o, k ∉ {i,j}, o ∉ {i,j} -/
lemma move_o_phi_swap {n : ℕ} (x : Fin n →₀ ℕ) (i j k o : Fin n) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (hoi : o ≠ i) (hoj : o ≠ j) :
    (x - e k + e o) - e i + e j = (x - e k + e j) - e i + e o := by
  ext t
  by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htk : t = k <;> by_cases hto : t = o
  all_goals simp_all [e, Finsupp.single_apply]
  all_goals omega

/-- Case: α ∈ A, β ∈ shiftSet, and the exchange happens at coordinate k = i. -/
lemma union_exch_AS_ki {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i ≠ j)
    {α β : Fin n →₀ ℕ} (hαA : α ∈ A) (hβS : β ∈ shiftSet A i j) (hgt : α i > β i) :
    ∃ l : Fin n, α l < β l ∧ α - e i + e l ∈ A ∪ shiftSet A i j := by
  let b : Fin n →₀ ℕ := β - e i + e j
  have hbA : b ∈ A := by simpa [b] using hβS.2
  have hβe : β = b + e i - e j := by
    simpa [b] using (shift_then_unshift β i j hij hβS.1).symm
  have hbj : 1 ≤ b j := by
    have hc : b j = β j + 1 := by simpa [b] using (sub_add_apply_j β i j hij)
    omega
  have hgtA : α i > b i := by
    have hβi : β i = b i + 1 := by rw [hβe, unshift_i b i j hij]
    omega
  have hαi1 : 1 ≤ α i := by omega
  rcases hA α hαA b hbA i hgtA with ⟨l, hltA, hmA⟩
  -- l ≠ i because α i < b i contradicts α i > b i
  have hβi : β i = b i + 1 := by rw [hβe, unshift_i b i j hij]
  have hβj' : β j = b j - 1 := by rw [hβe, unshift_j b i j hij hbj]
  have hli : l ≠ i := by
    intro h
    subst l
    omega
  by_cases hlj : l = j
  · -- l = j : the exchange moves a unit from i to j
    subst l
    have hαj_lt : α j < b j := hltA
    by_cases hαjβ : α j < β j
    · -- witness j directly (γ0 ∈ A)
      refine ⟨j, hαjβ, ?_⟩
      · have hβj : β j = b j - 1 := by rw [hβe, unshift_j b i j hij hbj]
        have hmem : α - e i + e j ∈ A := hmA
        exact Or.inl (by simpa using hmem)
    · -- leftover: α j = b j - 1 = β j; use the second exchange hA(γ0, b, i)
      have hαjb : α j = b j - 1 := by omega
      let γ0 : Fin n →₀ ℕ := α - e i + e j
      have hγ0A : γ0 ∈ A := by simpa [γ0] using hmA
      have hγ0i_val : γ0 i = α i - 1 := by simp [γ0, e, hij]
      have hγ0i : b i < γ0 i := by
        rw [hγ0i_val]
        omega
      rcases hA γ0 hγ0A b hbA i hγ0i with ⟨l', hlt', hm'⟩
      -- l' ∉ {i, j}:  (γ0 i > b i ⟹ l'≠i; γ0 j = b j ⟹ l'≠j)
      have hl'i : l' ≠ i := by
        intro h; subst l'; omega
      have hl'j : l' ≠ j := by
        intro h
        subst l'
        have hγ0j : γ0 j = b j := by
          have h1 : γ0 j = α j + 1 := by simp [γ0, e, hij]
          omega
        omega
      refine ⟨l', ?_, ?_⟩
      · -- α l' < β l' : β = b away from {i,j}
        have hαl' : α l' = γ0 l' := by simp [γ0, e, hl'i, hl'j]
        have hβl' : β l' = b l' := by
          rw [hβe, unshift_o b i j l' hl'i hl'j]
        omega
      · -- γ := α - e i + e l' ∈ S, with Φ γ = (γ0 - e i + e l') ∈ A
        let γ : Fin n →₀ ℕ := α - e i + e l'
        have hγphi : γ - e i + e j = γ0 - e i + e l' := by
          subst γ
          subst γ0
          -- both sides equal α - 2 e i + e j + e l'
          ext t
          by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l'
          all_goals simp_all [e, Finsupp.single_apply]
          all_goals omega
        have hγS : γ ∈ shiftSet A i j := by
          constructor
          · -- γ i ≥ 1 : γ i = α i - 1 ≥ 1 (α i > β i = b i + 1 ≥ 2)
            have hαi2 : 2 ≤ α i := by omega
            subst γ
            simp [e, Finsupp.single_apply]
            omega
          · have : γ - e i + e j ∈ A := by
              rw [hγphi]
              simpa [γ0] using hm'
            simpa [γ] using this
        exact Or.inr hγS
  · -- l ∉ {i, j} or (l = i impossible): witness l
    refine ⟨l, ?_, ?_⟩
    · -- α l < β l : for l ∉ {j} we have β l = b l (l ≠ i handled by hli but l = i impossible anyway)
      by_cases hli' : l = i
      · exfalso
        exact hli hli'
      · have hβl : β l = b l := by
          rw [hβe, unshift_o b i j l hli' hlj]
        omega
    · exact Or.inl hmA

/-- Case: α ∈ A, β ∈ shiftSet, exchange at coordinate k ∉ {i, j}. -/
lemma union_exch_AS_ko {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j k : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    {α β : Fin n →₀ ℕ} (hαA : α ∈ A) (hβS : β ∈ shiftSet A i j) (hgt : α k > β k) :
    ∃ l : Fin n, α l < β l ∧ α - e k + e l ∈ A ∪ shiftSet A i j := by
  let b : Fin n →₀ ℕ := β - e i + e j
  have hbA : b ∈ A := by simpa [b] using hβS.2
  have hβe : β = b + e i - e j := by
    simpa [b] using (shift_then_unshift β i j hij hβS.1).symm
  have hbj : 1 ≤ b j := by
    have hc : b j = β j + 1 := by simpa [b] using (sub_add_apply_j β i j hij)
    omega
  have hβi : β i = b i + 1 := by rw [hβe, unshift_i b i j hij]
  have hβk : β k = b k := by rw [hβe, unshift_o b i j k hki hkj]
  have hgtA : α k > b k := by omega
  rcases hA α hαA b hbA k hgtA with ⟨l, hltA, hmA⟩
  by_cases hli : l = i
  · -- witness l = i (a unit moved from k to i): γ0 = move(α,k,i) ∈ A
    subst l
    refine ⟨i, ?_, ?_⟩
    · have hβi' : β i = b i + 1 := hβi
      omega
    · exact Or.inl hmA
  · by_cases hlj : l = j
    · -- l = j: γ0 = move(α,k,j) ∈ A; inequality needs α j < β j
      subst l
      by_cases hαjβ : α j < β j
      · refine ⟨j, hαjβ, ?_⟩
        · exact Or.inl (by simpa using hmA)
      · -- leftover: α j = b j - 1 = β j
        have hβj : β j = b j - 1 := by rw [hβe, unshift_j b i j hij hbj]
        have hαjb : α j = b j - 1 := by omega
        let γ0 : Fin n →₀ ℕ := α - e k + e j
        have hγ0A : γ0 ∈ A := by simpa [γ0] using hmA
        by_cases hαi_le : α i ≤ b i
        · -- witness i: move(α,k,i) ∈ S with source γ0 ∈ A
          refine ⟨i, ?_, ?_⟩
          · have hβi' : β i = b i + 1 := hβi
            omega
          · let γ : Fin n →₀ ℕ := α - e k + e i
            have hγphi : γ - e i + e j = γ0 := by
              subst γ
              subst γ0
              exact move_i_then_shift α i j k
            have hγS : γ ∈ shiftSet A i j := by
              constructor
              · subst γ
                simp [e, Finsupp.single_apply]
              · have : γ - e i + e j ∈ A := by
                  rw [hγphi]
                  simpa [γ0] using hmA
                simpa [γ] using this
            exact Or.inr hγS
        · -- α i > b i : second exchange hA(γ0, b, i)
          have hαi_pos : 1 ≤ α i := by omega
          have hγ0i : b i < γ0 i := by
            have hγ0iv : γ0 i = α i := by simp [γ0, e, Finsupp.single_apply, hij, hki]
            rw [hγ0iv]
            omega
          rcases hA γ0 hγ0A b hbA i hγ0i with ⟨l', hlt', hm'⟩
          have hl'i : l' ≠ i := by
            intro h; subst l'; omega
          have hl'j : l' ≠ j := by
            intro h
            subst l'
            have hγ0j : γ0 j = α j + 1 := by simp [γ0, e, Finsupp.single_apply, hkj]
            omega
          have hl'k : l' ≠ k := by
            intro h
            subst l'
            have hγ0kv : γ0 k = α k - 1 := by simp [γ0, e, Finsupp.single_apply, hkj]
            omega
          refine ⟨l', ?_, ?_⟩
          · -- α l' < β l' : α l' = γ0 l' (since l' ∉ {i,j,k}) and γ0 l' < b l' = β l'
            have hαl' : α l' = γ0 l' := by simp [γ0, e, Finsupp.single_apply, hl'j, hl'k]
            have hβl' : β l' = b l' := by
              rw [hβe, unshift_o b i j l' hl'i hl'j]
            omega
          · -- γ := move(α,k,l') ∈ S with Φ γ = move(γ0,i,l') ∈ A
            let γ : Fin n →₀ ℕ := α - e k + e l'
            have hγphi : γ - e i + e j = γ0 - e i + e l' := by
              subst γ
              subst γ0
              exact move_o_phi_swap α i j k l' hij hki hkj hl'i hl'j
            have hγS : γ ∈ shiftSet A i j := by
              constructor
              · subst γ
                simp [e, Finsupp.single_apply, hki]
                omega
              · have : γ - e i + e j ∈ A := by
                  rw [hγphi]
                  simpa [γ0] using hm'
                simpa [γ] using this
            exact Or.inr hγS
    · -- l ∉ {i,j}: witness l, membership γ0 ∈ A
      refine ⟨l, ?_, ?_⟩
      · have hβl : β l = b l := by
          rw [hβe, unshift_o b i j l hli hlj]
        omega
      · exact Or.inl hmA

/-- Case: α ∈ A, β ∈ shiftSet, exchange at coordinate k = j. -/
lemma union_exch_AS_kj {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i ≠ j)
    {α β : Fin n →₀ ℕ} (hαA : α ∈ A) (hβS : β ∈ shiftSet A i j) (hgt : α j > β j) :
    ∃ l : Fin n, α l < β l ∧ α - e j + e l ∈ A ∪ shiftSet A i j := by
  let b : Fin n →₀ ℕ := β - e i + e j
  have hbA : b ∈ A := by simpa [b] using hβS.2
  have hβe : β = b + e i - e j := by
    simpa [b] using (shift_then_unshift β i j hij hβS.1).symm
  have hbj : 1 ≤ b j := by
    have hc : b j = β j + 1 := by simpa [b] using (sub_add_apply_j β i j hij)
    omega
  have hβi : β i = b i + 1 := by rw [hβe, unshift_i b i j hij]
  have hβj : β j = b j - 1 := by rw [hβe, unshift_j b i j hij hbj]
  have hgtA_j : α j ≥ b j := by omega
  have hαj1 : 1 ≤ α j := by omega
  by_cases hαj_b : b j + 1 ≤ α j
  · -- α j ≥ b j + 1: hA(α,b,j) applies
    have hgtA : α j > b j := by omega
    rcases hA α hαA b hbA j hgtA with ⟨l, hltA, hmA⟩
    have hlj : l ≠ j := by
      intro h; subst l; omega
    by_cases hli : l = i
    · subst l
      refine ⟨i, ?_, ?_⟩
      · omega
      · exact Or.inl hmA
    · refine ⟨l, ?_, ?_⟩
      · have hβl : β l = b l := by
          rw [hβe, unshift_o b i j l hli hlj]
        omega
      · exact Or.inl hmA
  · -- α j = b j (since α j ≥ b j and ¬(b j + 1 ≤ α j))
    have hαjb : α j = b j := by omega
    by_cases hαi_le : α i ≤ b i
    · -- witness i : move(α,j,i) ∈ S with Φ = α ∈ A
      refine ⟨i, ?_, ?_⟩
      · have hβi' : β i = b i + 1 := hβi
        omega
      · let γ : Fin n →₀ ℕ := α - e j + e i
        have hγphi : γ - e i + e j = α := by
          subst γ
          exact move_j_i_roundtrip α i j hij hαj1
        have hγS : γ ∈ shiftSet A i j := by
          constructor
          · subst γ
            simp [e, Finsupp.single_apply]
          · have : γ - e i + e j ∈ A := by
              rw [hγphi]
              exact hαA
            simpa [γ] using this
        exact Or.inr hγS
    · -- α i > b i : hA(α,b,i) gives l ∉ {i,j}; witness l
      have hgtAi : α i > b i := by omega
      rcases hA α hαA b hbA i hgtAi with ⟨l, hltA, hmA⟩
      have hli : l ≠ i := by intro h; subst l; omega
      have hlj : l ≠ j := by intro h; subst l; omega
      refine ⟨l, ?_, ?_⟩
      · -- α l < β l = b l
        have hβl : β l = b l := by
          rw [hβe, unshift_o b i j l hli hlj]
        omega
      · -- γ := move(α,j,l) ∈ S with Φ γ = move(α,i,l) ∈ A
        let γ : Fin n →₀ ℕ := α - e j + e l
        have hγphi : γ - e i + e j = α - e i + e l := by
          subst γ
          exact move_j_o_phi α i j l hij hli hlj hαj1
        have hγS : γ ∈ shiftSet A i j := by
          constructor
          · subst γ
            simp [e, Finsupp.single_apply, hli, hij]
            omega
          · have : γ - e i + e j ∈ A := by
              rw [hγphi]
              exact hmA
            simpa [γ] using this
        exact Or.inr hγS

/-- The (α ∈ A, β ∈ shiftSet) exchange case, dispatched by the exchange coordinate. -/
lemma union_exch_AS {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i ≠ j)
    {α β : Fin n →₀ ℕ} (k : Fin n) (hαA : α ∈ A) (hβS : β ∈ shiftSet A i j) (hgt : α k > β k) :
    ∃ l : Fin n, α l < β l ∧ α - e k + e l ∈ A ∪ shiftSet A i j := by
  by_cases hki : k = i
  · subst k
    exact union_exch_AS_ki hA hij hαA hβS hgt
  · by_cases hkj : k = j
    · subst k
      exact union_exch_AS_kj hA hij hαA hβS hgt
    · exact union_exch_AS_ko hA hij hki hkj hαA hβS hgt



/-- membership in the shifted set with source `a` -/
lemma mem_shift_of_source {n : ℕ} (A : Set (Fin n →₀ ℕ)) (i j : Fin n) (hij : i ≠ j)
    {a α : Fin n →₀ ℕ} (haj : 1 ≤ a j) (hα : α = a + e i - e j) (ha : a ∈ A) :
    α ∈ shiftSet A i j := by
  constructor
  · rw [hα, unshift_i a i j hij]
    omega
  · rw [hα, unshift_then_shift a i j hij haj]
    exact ha

/-- Case: α ∈ shiftSet, β ∈ A, exchange at coordinate k ∉ {i, j}. -/
lemma union_exch_SA_ko {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j k : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    {α β : Fin n →₀ ℕ} (hαS : α ∈ shiftSet A i j) (hβA : β ∈ A) (hgt : α k > β k) :
    ∃ l : Fin n, α l < β l ∧ α - e k + e l ∈ A ∪ shiftSet A i j := by
  let a : Fin n →₀ ℕ := α - e i + e j
  have haA : a ∈ A := by simpa [a] using hαS.2
  have hαe : α = a + e i - e j := by
    simpa [a] using (shift_then_unshift α i j hij hαS.1).symm
  have haj : 1 ≤ a j := by
    have hc : a j = α j + 1 := by simpa [a] using (sub_add_apply_j α i j hij)
    omega
  have hαk : α k = a k := by rw [hαe, unshift_o a i j k hki hkj]
  have hgtA : a k > β k := by omega
  rcases hA a haA β hβA k hgtA with ⟨l, hltA, hmA⟩
  by_cases hli : l = i
  · -- l = i : the exchange moves a unit from k to i inside the source; witness i (in S) if α i < β i
    subst l
    by_cases hαiβ : α i < β i
    · refine ⟨i, hαiβ, ?_⟩
      · -- move(α,k,i) ∈ S with source γ0 = a - e k + e i ∈ A
        let γ : Fin n →₀ ℕ := α - e k + e i
        have hγphi : γ - e i + e j = a - e k + e i := by
          subst γ
          rw [hαe]
          exact shift_move_out a i j k i hij hki hkj haj
        have hγS : γ ∈ shiftSet A i j := by
          constructor
          · subst γ
            simp [e, Finsupp.single_apply, hki]
          · have : γ - e i + e j ∈ A := by
              rw [hγphi]
              exact hmA
            simpa [γ] using this
        exact Or.inr hγS
    · -- leftover: α i ≥ β i (indeed = β i since a i < β i and α i = a i + 1)
      by_cases hajβ : a j ≤ β j
      · -- witness j (in A, via γ0 = move(α,k,j) = move(a,k,i) = move(a,k,i) ∈ A)
        refine ⟨j, ?_, ?_⟩
        · -- α j = a j - 1 < β j since a j ≤ β j
          have hαj : α j = a j - 1 := by rw [hαe, unshift_j a i j hij haj]
          omega
        · -- move(α,k,j) = γ0 := move(a,k,i) ∈ A
          have hγ0A : a - e k + e i ∈ A := hmA
          let γ : Fin n →₀ ℕ := α - e k + e j
          have hγeq : γ = a - e k + e i := by
            subst γ
            rw [hαe]
            -- (a + e_i - e_j) - e_k + e_j = a - e_k + e_i
            ext t
            by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htk : t = k
            all_goals simp_all [e, Finsupp.single_apply]
            all_goals omega
          exact Or.inl (by simpa [γ, hγeq] using hγ0A)
      · -- a j > β j : second exchange hA(γ0, β, j) where γ0 = move(a,k,i)
        let γ0 : Fin n →₀ ℕ := a - e k + e i
        have hγ0A : γ0 ∈ A := by simpa [γ0] using hmA
        have hγ0j : β j < γ0 j := by
          have hγ0jv : γ0 j = a j := by simp [γ0, e, hij, hkj]
          omega
        rcases hA γ0 hγ0A β hβA j hγ0j with ⟨l', hlt', hm'⟩
        have hl'i : l' ≠ i := by
          intro h; subst l'
          have hzk : (e k) i = 0 := Finsupp.single_eq_of_ne (a := k) (b := (1 : ℕ)) (a' := i) (by intro hik; exact hki hik.symm)
          have hγ0iv : γ0 i = a i + 1 := by simp [γ0, e, hzk]
          have hαiv : α i = a i + 1 := by rw [hαe, unshift_i a i j hij]
          omega
        have hl'j : l' ≠ j := by intro h; subst l'; omega
        have hl'k : l' ≠ k := by
          intro h; subst l'
          have hzk : (e i) k = 0 := Finsupp.single_eq_of_ne (a := i) (b := (1 : ℕ)) (a' := k) hki
          have hγ0kv : γ0 k = a k - 1 := by simp [γ0, e, hzk]
          omega
        refine ⟨l', ?_, ?_⟩
        · -- α l' < β l' : α l' = γ0 l' (l' ∉ {i,j}) and γ0 l' < β l'
          have hαl' : α l' = γ0 l' := by
            have hγ0lv : γ0 l' = a l' := by simp [γ0, e, hl'i, hl'j, hl'k]
            have hαlv : α l' = a l' := by
              rw [hαe, unshift_o a i j l' hl'i hl'j]
            omega
          omega
        · -- move(α,k,l') = move(γ0,j,l') ∈ A
          let γ : Fin n →₀ ℕ := α - e k + e l'
          have hγeq : γ = γ0 - e j + e l' := by
            subst γ
            subst γ0
            rw [hαe]
            ext t
            by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htk : t = k <;> by_cases htl : t = l'
            all_goals simp_all [e, Finsupp.single_apply]
            all_goals omega
          exact Or.inl (by simpa [γ, hγeq] using hm')
  · by_cases hlj : l = j
    · -- l = j : witness j (in S)
      subst l
      refine ⟨j, ?_, ?_⟩
      · -- α j = a j - 1 < β j, from a j < β j
        have hαj : α j = a j - 1 := by rw [hαe, unshift_j a i j hij haj]
        omega
      · let γ : Fin n →₀ ℕ := α - e k + e j
        have hγphi : γ - e i + e j = a - e k + e j := by
          subst γ
          rw [hαe]
          exact shift_move_out a i j k j hij hki hkj haj
        have hγS : γ ∈ shiftSet A i j := by
          constructor
          · subst γ
            simp_all [e, Finsupp.single_apply]
          · have : γ - e i + e j ∈ A := by
              rw [hγphi]
              exact hmA
            simpa [γ] using this
        exact Or.inr hγS
    · -- l ∉ {i,j} : witness l (in S)
      refine ⟨l, ?_, ?_⟩
      · have hαl : α l = a l := by rw [hαe, unshift_o a i j l hli hlj]
        omega
      · let γ : Fin n →₀ ℕ := α - e k + e l
        have hγphi : γ - e i + e j = a - e k + e l := by
          subst γ
          rw [hαe]
          exact shift_move_out a i j k l hij hki hkj haj
        have hγS : γ ∈ shiftSet A i j := by
          constructor
          · subst γ
            simp_all [e, Finsupp.single_apply]
          · have : γ - e i + e j ∈ A := by
              rw [hγphi]
              exact hmA
            simpa [γ] using this
        exact Or.inr hγS
/-- Case: α ∈ shiftSet, β ∈ A, exchange at coordinate k = j. -/
lemma union_exch_SA_kj {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i ≠ j)
    {α β : Fin n →₀ ℕ} (hαS : α ∈ shiftSet A i j) (hβA : β ∈ A) (hgt : α j > β j) :
    ∃ l : Fin n, α l < β l ∧ α - e j + e l ∈ A ∪ shiftSet A i j := by
  let a : Fin n →₀ ℕ := α - e i + e j
  have haA : a ∈ A := by simpa [a] using hαS.2
  have hαe : α = a + e i - e j := by
    simpa [a] using (shift_then_unshift α i j hij hαS.1).symm
  have haj : 1 ≤ a j := by
    have hc : a j = α j + 1 := by simpa [a] using (sub_add_apply_j α i j hij)
    omega
  have hαj : α j = a j - 1 := by rw [hαe, unshift_j a i j hij haj]
  have hgtA : a j > β j := by omega
  have haj2 : 2 ≤ a j := by omega
  rcases hA a haA β hβA j hgtA with ⟨l, hltA, hmA⟩
  have hlj : l ≠ j := by intro h; subst l; omega
  by_cases hli : l = i
  · -- l = i : γ0 = move(a,j,i) ∈ A
    subst l
    by_cases hαiβ : α i < β i
    · -- witness i (in S)
      refine ⟨i, hαiβ, ?_⟩
      · let γ : Fin n →₀ ℕ := α - e j + e i
        have hγphi : γ - e i + e j = a - e j + e i := by
          subst γ
          rw [hαe]
          exact shift_move_kj a i j i hij haj2
        have hγS : γ ∈ shiftSet A i j := by
          constructor
          · subst γ
            simp [e, Finsupp.single_apply, hij]
          · have : γ - e i + e j ∈ A := by
              rw [hγphi]
              exact hmA
            simpa [γ] using this
        exact Or.inr hγS
    · -- leftover α i ≥ β i: second exchange hA(γ0, β, j), γ0 = move(a,j,i)
      let γ0 : Fin n →₀ ℕ := a - e j + e i
      have hγ0A : γ0 ∈ A := by simpa [γ0] using hmA
      have hγ0j : β j < γ0 j := by
        have hz : (e i) j = 0 := Finsupp.single_eq_of_ne (a := i) (b := (1 : ℕ)) (a' := j) hij.symm
        have hγ0jv : γ0 j = a j - 1 := by simp [γ0, e, hz]
        omega
      rcases hA γ0 hγ0A β hβA j hγ0j with ⟨l', hlt', hm'⟩
      have hl'i : l' ≠ i := by
        intro h; subst l'
        have hγ0iv : γ0 i = a i + 1 := by simp [γ0, e, hij]
        have hαiv : α i = a i + 1 := by rw [hαe, unshift_i a i j hij]
        omega
      have hl'j : l' ≠ j := by intro h; subst l'; omega
      refine ⟨l', ?_, ?_⟩
      · -- α l' < β l' = γ0 l' < β l'
        have hγ0lv : γ0 l' = a l' := by simp [γ0, e, hl'i, hl'j, hij]
        have hαlv : α l' = a l' := by rw [hαe, unshift_o a i j l' hl'i hl'j]
        omega
      · -- move(α,j,l') = move(γ0,j,l') ∈ A
        let γ : Fin n →₀ ℕ := α - e j + e l'
        have hγeq : γ = γ0 - e j + e l' := by
          subst γ
          subst γ0
          rw [hαe]
          ext t
          by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l'
          all_goals simp_all [e, Finsupp.single_apply]
          all_goals omega
        exact Or.inl (by simpa [γ, hγeq] using hm')
  · -- l ∉ {i, j}: witness l (in S)
    refine ⟨l, ?_, ?_⟩
    · have hαl : α l = a l := by rw [hαe, unshift_o a i j l hli hlj]
      omega
    · let γ : Fin n →₀ ℕ := α - e j + e l
      have hγphi : γ - e i + e j = a - e j + e l := by
        subst γ
        rw [hαe]
        exact shift_move_kj a i j l hij haj2
      have hγS : γ ∈ shiftSet A i j := by
        constructor
        · subst γ
          simp_all [e, Finsupp.single_apply]
        · have : γ - e i + e j ∈ A := by
            rw [hγphi]
            exact hmA
          simpa [γ] using this
      exact Or.inr hγS


/-- Case: α ∈ shiftSet, β ∈ A, exchange at coordinate k = i. -/
lemma union_exch_SA_ki {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i ≠ j)
    {α β : Fin n →₀ ℕ} (hαS : α ∈ shiftSet A i j) (hβA : β ∈ A) (hgt : α i > β i) :
    ∃ l : Fin n, α l < β l ∧ α - e i + e l ∈ A ∪ shiftSet A i j := by
  let a : Fin n →₀ ℕ := α - e i + e j
  have haA : a ∈ A := by simpa [a] using hαS.2
  have hαe : α = a + e i - e j := by
    simpa [a] using (shift_then_unshift α i j hij hαS.1).symm
  have haj : 1 ≤ a j := by
    have hc : a j = α j + 1 := by simpa [a] using (sub_add_apply_j α i j hij)
    omega
  have hαi : α i = a i + 1 := by rw [hαe, unshift_i a i j hij]
  by_cases haigb : a i > β i
  · -- a i > β i : hA(a, β, i) applies
    have hai1 : 1 ≤ a i := by omega
    rcases hA a haA β hβA i haigb with ⟨l, hltA, hmA⟩
    have hli : l ≠ i := by intro h; subst l; omega
    by_cases hlj : l = j
    · -- l = j : witness j (in S)
      subst l
      refine ⟨j, ?_, ?_⟩
      · -- α j = a j - 1 < β j (since a j < β j)
        have hαj : α j = a j - 1 := by rw [hαe, unshift_j a i j hij haj]
        omega
      · let γ : Fin n →₀ ℕ := α - e i + e j
        have hγphi : γ - e i + e j = a - e i + e j := by
          subst γ
          rw [hαe]
          exact shift_move_ki a i j j hij hai1 haj
        have hγS : γ ∈ shiftSet A i j := by
          constructor
          · subst γ
            simp_all [e, Finsupp.single_apply]
          · have : γ - e i + e j ∈ A := by
              rw [hγphi]
              exact hmA
            simpa [γ] using this
        exact Or.inr hγS
    · -- l ∉ {i, j}: witness l (in S)
      refine ⟨l, ?_, ?_⟩
      · have hαl : α l = a l := by rw [hαe, unshift_o a i j l hli hlj]
        omega
      · let γ : Fin n →₀ ℕ := α - e i + e l
        have hγphi : γ - e i + e j = a - e i + e l := by
          subst γ
          rw [hαe]
          exact shift_move_ki a i j l hij hai1 haj
        have hγS : γ ∈ shiftSet A i j := by
          constructor
          · subst γ
            simp_all [e, Finsupp.single_apply]
          · have : γ - e i + e j ∈ A := by
              rw [hγphi]
              exact hmA
            simpa [γ] using this
        exact Or.inr hγS
  · -- a i = β i (since α i = a i + 1 > β i)
    have haib : a i = β i := by omega
    by_cases hajβ : a j ≤ β j
    · -- witness j : move(α,i,j) = a ∈ A
      refine ⟨j, ?_, ?_⟩
      · have hαj : α j = a j - 1 := by rw [hαe, unshift_j a i j hij haj]
        omega
      · let γ : Fin n →₀ ℕ := α - e i + e j
        have hγeq : γ = a := by
          subst γ
          rw [hαe]
          calc
            (a + e i - e j) - e i + e j = (a + e i - e i) - e j + e j := by
              rw [sub_sub_comm (a + e i) j i]
            _ = (a - e j) + e j := by rw [add_sub_single a i]
            _ = a := by rw [sub_single_add_self a j haj]
        exact Or.inl (by simpa [γ, hγeq] using haA)
    · -- a j > β j : hA(a, β, j) gives the witness (move(α,i,l') = move(a,j,l') ∈ A)
      have hgtAj : a j > β j := by omega
      rcases hA a haA β hβA j hgtAj with ⟨l', hlt', hm'⟩
      have hl'j : l' ≠ j := by intro h; subst l'; omega
      by_cases hl'i : l' = i
      · -- l' = i would need a i < β i, false since a i = β i
        exfalso
        subst l'
        omega
      · refine ⟨l', ?_, ?_⟩
        · -- α l' < β l' = a l' < β l' (l' ∉ {i,j})
          have hαl' : α l' = a l' := by rw [hαe, unshift_o a i j l' hl'i hl'j]
          omega
        · -- move(α,i,l') = move(a,j,l') ∈ A
          let γ : Fin n →₀ ℕ := α - e i + e l'
          have hγeq : γ = a - e j + e l' := by
            subst γ
            rw [hαe]
            -- (a + e_i - e_j) - e_i + e_l' = a - e_j + e_l'
            calc
              (a + e i - e j) - e i + e l' = ((a + e i) - e i) - e j + e l' := by
                rw [sub_sub_comm (a + e i) j i]
              _ = (a - e j) + e l' := by rw [add_sub_single a i]
              _ = a - e j + e l' := rfl
          exact Or.inl (by simpa [γ, hγeq] using hm')

/-- The (α ∈ shiftSet, β ∈ A) exchange case, dispatched by the exchange coordinate. -/
lemma union_exch_SA {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i ≠ j)
    {α β : Fin n →₀ ℕ} (k : Fin n) (hαS : α ∈ shiftSet A i j) (hβA : β ∈ A) (hgt : α k > β k) :
    ∃ l : Fin n, α l < β l ∧ α - e k + e l ∈ A ∪ shiftSet A i j := by
  by_cases hki : k = i
  · subst k
    exact union_exch_SA_ki hA hij hαS hβA hgt
  · by_cases hkj : k = j
    · subst k
      exact union_exch_SA_kj hA hij hαS hβA hgt
    · exact union_exch_SA_ko hA hij hki hkj hαS hβA hgt




/-- Case: both endpoints are in `A`: directly from the exchange property of `A`. -/
lemma union_exch_AA {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) {α β : Fin n →₀ ℕ} (k : Fin n)
    (hαA : α ∈ A) (hβA : β ∈ A) (hgt : α k > β k) :
    ∃ l : Fin n, α l < β l ∧ α - e k + e l ∈ A ∪ shiftSet A i j := by
  rcases hA α hαA β hβA k hgt with ⟨l, hlt, hmem⟩
  exact ⟨l, hlt, Or.inl hmem⟩

/-- If `i = j` the shift adds nothing: the union is just `A`, which is M-convex. -/
lemma union_exch_eq {n : ℕ} {A : Set (Fin n →₀ ℕ)} {i j : Fin n}
    (hA : Commons.LorentzianPolynomials.IsMConvex A) (hij : i = j) :
    Commons.LorentzianPolynomials.IsMConvex (A ∪ shiftSet A i j) := by
  subst j
  unfold Commons.LorentzianPolynomials.IsMConvex at hA ⊢
  intro α hα β hβ k hgt
  have hαA : α ∈ A := by
    rcases hα with hαA | hαS
    · exact hαA
    · exact shiftSet_self_subset A i hαS
  have hβA : β ∈ A := by
    rcases hβ with hβA | hβS
    · exact hβA
    · exact shiftSet_self_subset A i hβS
  rcases hA α hαA β hβA k hgt with ⟨l, hlt, hmem⟩
  exact ⟨l, hlt, Or.inl hmem⟩

/-! ### The main theorem -/

theorem union_shift_mconvex {n : ℕ} (A : Set (Fin n →₀ ℕ)) (i j : Fin n)
    (hA : Commons.LorentzianPolynomials.IsMConvex A) :
    Commons.LorentzianPolynomials.IsMConvex
      (A ∪ {m : Fin n →₀ ℕ | m i ≥ 1 ∧ m - Finsupp.single i 1 + Finsupp.single j 1 ∈ A}) := by
  change Commons.LorentzianPolynomials.IsMConvex (A ∪ shiftSet A i j)
  by_cases hij : i = j
  · exact union_exch_eq hA hij
  · unfold Commons.LorentzianPolynomials.IsMConvex
    intro α hα β hβ k hgt
    by_cases hβA : β ∈ A
    · rcases hα with hαA | hαS
      · exact union_exch_AA hA k hαA hβA hgt
      · exact union_exch_SA hA hij k hαS hβA hgt
    · have hβS : β ∈ shiftSet A i j := by
        rcases hβ with hβA' | hβS
        · exact False.elim (hβA hβA')
        · exact hβS
      rcases hα with hαA | hαS
      · exact union_exch_AS hA hij k hαA hβS hgt
      · exact union_exch_SS hA hij k hαS hβS hgt


end
end Commons.Combinatorics.MvPolynomial
