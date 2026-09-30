import Mathlib
import ChallengeDeps
import Submission.Work.BW.Defs
import Submission.Work.BW.kummer_residue

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Baker–Wüstholz §9: the Kummer reduction

`Work.BW.kummer_reduction`: given `ℚ`-linearly independent principal logarithms `log (φ (α i))`
and a Lehmer-type constant `c' > 1`, there are `v : ℕ`, an integral matrix `L` invertible over
`ℚ`, `α' j ∈ K` and `σ j > 0` with `BH φ α b v (c'^n n!) n L α' σ`.

The proof follows BW §9: an induction on the level `v` produces states `(ν, m, β)` with
`exp (2^{-v} ∑_i m_ij log (φ (α i))) = φ (β_j)`; as long as the Kummer condition fails one
column can be replaced (Kummer descent), and Minkowski's second inequality combined with the
height lower bound `hLeh` bounds `v`.  At the stopping state one of two constructions gives `BH`.
-/

namespace Work.BW

open Complex

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- BW's modified height `h'(β)`. -/
noncomputable abbrev hp (φ : K →+* ℂ) (β : K) : ℝ := BakerWustholz.modifiedHeight φ β

lemma hp_def (φ : K →+* ℂ) (β : K) :
    hp φ β = max (Height.logHeight₁ β / (Module.finrank ℚ K : ℝ))
      (max (‖Complex.log (φ β)‖ / (Module.finrank ℚ K : ℝ))
        (1 / (Module.finrank ℚ K : ℝ))) := rfl

lemma one_div_finrank_le_hp (φ : K →+* ℂ) (β : K) :
    1 / (Module.finrank ℚ K : ℝ) ≤ hp φ β := by
  rw [hp_def]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

lemma hp_pos (φ : K →+* ℂ) (β : K) : 0 < hp φ β := by
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  exact lt_of_lt_of_le (div_pos one_pos hd) (one_div_finrank_le_hp φ β)

lemma logHeight_div_le_hp (φ : K →+* ℂ) (β : K) :
    Height.logHeight₁ β / (Module.finrank ℚ K : ℝ) ≤ hp φ β := by
  rw [hp_def]; exact le_max_left _ _

lemma log_div_le_hp (φ : K →+* ℂ) (β : K) :
    ‖Complex.log (φ β)‖ / (Module.finrank ℚ K : ℝ) ≤ hp φ β := by
  rw [hp_def]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- BW §9: `σ_j = max (h'(α_j)) ((j+1)/2 * h'(α_j))` (with `j` the zero-based index). -/
noncomputable def sig (φ : K →+* ℂ) (α : Fin n → K) (j : Fin n) : ℝ :=
  max (hp φ (α j)) ((((j : ℝ) + 1) / 2) * hp φ (α j))

lemma hp_le_sig (φ : K →+* ℂ) (α : Fin n → K) (j : Fin n) :
    hp φ (α j) ≤ sig φ α j := le_max_left _ _

lemma half_mul_hp_le_sig (φ : K →+* ℂ) (α : Fin n → K) (j : Fin n) :
    (((j : ℝ) + 1) / 2) * hp φ (α j) ≤ sig φ α j := le_max_right _ _

lemma sig_pos (φ : K →+* ℂ) (α : Fin n → K) (j : Fin n) : 0 < sig φ α j :=
  lt_of_lt_of_le (hp_pos φ (α j)) (hp_le_sig φ α j)

/-- State of the BW §9 induction at level `s.v`. -/
structure KSt (K : Type*) [Field K] (n : ℕ) where
  /-- level -/
  v : ℕ
  /-- exponents `ν_j` -/
  nu : Fin n → ℕ
  /-- integral matrix `m` -/
  m : Matrix (Fin n) (Fin n) ℤ
  /-- elements `α_j^{(ν)}` -/
  β : Fin n → K

/-- The inductive invariant of BW §9. -/
structure Inv (φ : K →+* ℂ) (α : Fin n → K) (s : KSt K n) : Prop where
  beta_ne : ∀ j, s.β j ≠ 0
  sum_nu : ∑ j, s.nu j = s.v
  tri : ∀ i j, j < i → s.m i j = 0
  diag : ∀ j, s.m j j = (2 : ℤ) ^ (s.v - s.nu j)
  exp_eq : ∀ j, Complex.exp (((2 : ℂ) ^ s.v)⁻¹ *
      ∑ i, (s.m i j : ℂ) * Complex.log (φ (α i))) = φ (s.β j)
  colsum : ∀ j, ∑ i, |(s.m i j : ℝ)| * hp φ (α i) ≤ (2 : ℝ) ^ s.v * sig φ α j

lemma Inv.nu_le {φ : K →+* ℂ} {α : Fin n → K} {s : KSt K n}
    (h : Inv φ α s) (j : Fin n) : s.nu j ≤ s.v := by
  have hsum := h.sum_nu
  calc s.nu j ≤ ∑ j, s.nu j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = s.v := hsum

/-- The initial state: `α_j^{(0)} = α_j`, `m = 1`, `v = ν = 0`. -/
def S0 (α : Fin n → K) : KSt K n :=
  ⟨0, fun _ => 0, fun i j => if i = j then 1 else 0, α⟩

lemma S0_m (α : Fin n → K) (i j : Fin n) :
    (S0 α).m i j = if i = j then 1 else 0 := rfl

lemma S0_v (α : Fin n → K) : (S0 α).v = 0 := rfl

lemma S0_beta (α : Fin n → K) : (S0 α).β = α := rfl

lemma S0_nu (α : Fin n → K) : (S0 α).nu = fun _ => 0 := rfl

lemma inv_S0 (φ : K →+* ℂ) (α : Fin n → K) (hα : ∀ i, α i ≠ 0) : Inv φ α (S0 α) := by
  have hnm : ∀ (j : Fin n), ((S0 α).m j j) = 1 := by
    intro j; rw [S0_m]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [S0_beta]; exact hα j
  · simp [S0]
  · intro i j hij
    rw [S0_m]
    simp only [if_neg (ne_of_gt hij)]
  · intro j
    have hd : (S0 α).v - (S0 α).nu j = 0 := by simp [S0]
    rw [hd, hnm j]; norm_num
  · intro j
    have hsum : (∑ i, ((S0 α).m i j : ℂ) * Complex.log (φ (α i)))
        = Complex.log (φ (α j)) := by
      rw [Finset.sum_eq_single j]
      · rw [S0_m]; simp
      · intro i _ hij; rw [S0_m]; simp [hij]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [S0_v, hsum]
    simp only [pow_zero, inv_one, one_mul]
    rw [S0_beta]
    exact Complex.exp_log (by simpa using hα j)
  · intro j
    have hsum : (∑ i, |((S0 α).m i j : ℝ)| * hp φ (α i)) = hp φ (α j) := by
      rw [Finset.sum_eq_single j]
      · rw [S0_m]; simp
      · intro i _ hij; rw [S0_m]; simp [hij]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [S0_v, hsum]
    simpa using hp_le_sig φ α j

open scoped Classical

/-- The number of `i : Fin n` with `i ≤ k` is `k + 1`. -/
lemma card_filter_le {n : ℕ} (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => i ≤ k)).card = (k : ℕ) + 1 := by
  rw [← Finset.card_range ((k : ℕ) + 1)]
  refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (by exact_mod_cast hi)
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro m hm
    simp only [Finset.mem_range] at hm
    have hmk : m ≤ (k : ℕ) := Nat.lt_succ_iff.mp hm
    have hmn : m < n := lt_of_le_of_lt hmk k.isLt
    refine ⟨⟨m, hmn⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact_mod_cast hmk

/-- One Kummer descent step: from a state satisfying `Inv` in which the Kummer condition fails,
produce a state at level `v+1` again satisfying `Inv`. -/
theorem step_exists (φ : K →+* ℂ) (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (hsort : ∀ i j : Fin n, i ≤ j → hp φ (α i) ≤ hp φ (α j))
    (s : KSt K n) (hs : Inv φ α s) (hK : ¬ KummerCond s.β) :
    ∃ s' : KSt K n, Inv φ α s' ∧ s'.v = s.v + 1 := by
  classical
  -- Kummer-failing data
  obtain ⟨e, γ, he, hγ⟩ : ∃ (e : Fin n → Fin 2) (γ : K),
      e ≠ 0 ∧ γ ^ 2 = ∏ i, (s.β i) ^ ((e i : ℕ)) := by
    by_contra hcon
    push_neg at hcon
    refine hK fun e he hsq => ?_
    obtain ⟨γ, hγ⟩ := hsq
    exact hcon e γ he (by rw [pow_two]; exact hγ.symm)
  -- the largest index with `e k ≠ 0`
  obtain ⟨k, hkmem, hkle⟩ : ∃ k : Fin n, e k ≠ 0 ∧ ∀ i, e i ≠ 0 → i ≤ k := by
    set S := Finset.univ.filter (fun i : Fin n => e i ≠ 0) with hSdef
    have hSne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      refine he (funext fun i => ?_)
      have : i ∉ S := by rw [hemp]; simp
      simpa [hSdef] using this
    refine ⟨S.max' hSne, ?_, ?_⟩
    · simpa [hSdef] using Finset.max'_mem S hSne
    · intro i hi
      exact Finset.le_max' S i (by simp [hSdef, hi])
  have hek1 : e k = 1 := by
    have h2 : (e k : ℕ) ≠ 0 := fun h => hkmem (by ext; simpa using h)
    have h3 : (e k : ℕ) = 1 := by have := (e k).isLt; omega
    exact Fin.ext h3
  have hek : (e k : ℤ) = 1 := by rw [hek1]; rfl
  have hkgt : ∀ i, k < i → e i = 0 := by
    intro i hi
    by_contra hne
    exact absurd (hkle i hne) (not_le.mpr hi)
  -- the integer vector `A`
  set A : Fin n → ℤ := fun a => ∑ i, (e i : ℤ) * s.m a i with hAdef
  have hA_zero : ∀ a, k < a → A a = 0 := by
    intro a ha
    simp only [hAdef]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hik : i ≤ k
    · have h1 : s.m a i = 0 := hs.tri a i (lt_of_le_of_lt hik ha)
      simp [h1]
    · have h1 : e i = 0 := hkgt i (not_le.mp hik)
      simp [h1]
  have hA_k : A k = s.m k k := by
    simp only [hAdef]
    have h1 : (∑ i, (e i : ℤ) * s.m k i) = (e k : ℤ) * s.m k k := by
      rw [Finset.sum_eq_single k]
      · intro i _ hik
        rcases lt_or_gt_of_ne hik with hlt | hgt
        · have h2 : s.m k i = 0 := hs.tri k i hlt
          simp [h2]
        · have h2 : e i = 0 := hkgt i hgt
          simp [h2]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [h1, hek, one_mul]
  -- residues of `A` mod `2^(v+1)`, with the `k`-th coordinate left equal to `A k`
  choose r r' hr using fun a => kummer_residue s.v (A a)
  have hr' : ∀ a, A a = r a + 2 ^ (s.v + 1) * r' a ∧ |r a| ≤ 2 ^ s.v := hr
  set t : Fin n → ℤ := fun a => if a = k then 0 else r' a with htdef
  set m' : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    if j = k then (if i = k then A k else r i) else 2 * s.m i j with hm'def
  have ht_spec : ∀ a, 2 ^ (s.v + 1) * t a = A a - m' a k := by
    intro a
    by_cases hak : a = k
    · subst hak
      simp [htdef, hm'def, hA_k]
    · have hm : m' a k = r a := by simp [hm'def, hak]
      have ht : t a = r' a := by simp [htdef, hak]
      rw [hm, ht]
      have := (hr' a).1
      linarith
  have hr_zero : ∀ a, k < a → m' a k = 0 := by
    intro a ha
    have hAc : A a = 0 := hA_zero a ha
    have hm : m' a k = r a := by
      simp only [hm'def, if_true, if_neg (ne_of_gt ha)]
    rw [hm]
    have h1 := (hr' a).1
    have h2 : |r a| ≤ 2 ^ s.v := (hr' a).2
    have h3 : r a = -(2 : ℤ) ^ (s.v + 1) * r' a := by linarith
    have hr'a : r' a = 0 := by
      by_contra hne
      have h4 : (1 : ℤ) ≤ |r' a| := by have := abs_pos.mpr hne; omega
      have h5 : (2 : ℤ) ^ (s.v + 1) ≤ |r a| := by
        rw [h3, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℤ) ≤ (2:ℤ) ^ (s.v+1))]
        exact le_mul_of_one_le_right (by positivity) h4
      have h6 : (2 : ℤ) ^ s.v < (2 : ℤ) ^ (s.v + 1) := by
        rw [pow_succ]
        have hp := pow_pos (by norm_num : (0:ℤ) < 2) s.v
        nlinarith
      omega
    rw [h3, hr'a]; ring

  -- the log vectors and the square-root element
  set L : Fin n → ℂ := fun a => Complex.log (φ (α a)) with hLdef
  set lam : Fin n → ℂ := fun i => ((2:ℂ)^s.v)⁻¹ * ∑ a, (s.m a i : ℂ) * L a with hlamdef
  set w : ℂ := Complex.exp (((2:ℂ)^(s.v+1))⁻¹ * ∑ a, (A a : ℂ) * L a) with hwdef
  have hAeq : ∑ a, (A a : ℂ) * L a = (2:ℂ)^s.v * ∑ i, ((e i : ℕ) : ℂ) * lam i := by
    calc ∑ a, (A a : ℂ) * L a
        = ∑ a, (∑ i, (((e i : ℤ) : ℂ)) * (s.m a i : ℂ)) * L a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hAdef]; push_cast; rfl
      _ = ∑ i, ((e i : ℕ) : ℂ) * ∑ a, (s.m a i : ℂ) * L a := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          push_cast
          ring
      _ = (2:ℂ)^s.v * ∑ i, ((e i : ℕ) : ℂ) * lam i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hlamdef]
          have hne : ((2:ℂ)^s.v) ≠ 0 := pow_ne_zero _ (by norm_num)
          field_simp
  have hw2 : w ^ 2 = (φ γ) ^ 2 := by
    have h1 : w ^ 2 = Complex.exp (∑ i, ((e i : ℕ) : ℂ) * lam i) := by
      rw [hwdef, pow_two, ← Complex.exp_add]
      congr 1
      rw [hAeq]
      have hne : ((2:ℂ)^(s.v+1)) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      ring
    rw [h1, Complex.exp_sum]
    have h2 : ∏ i, Complex.exp (((e i : ℕ) : ℂ) * lam i)
        = φ (∏ i, (s.β i) ^ (e i : ℕ)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Complex.exp_nat_mul, map_pow]
      congr 1
      exact hs.exp_eq i
    rw [h2, ← hγ, map_pow]
  have hww : w * w = φ γ * φ γ := by rw [← pow_two, ← pow_two]; exact hw2
  obtain ⟨γ'', hwγ'', hγ''sq⟩ : ∃ γ'' : K, w = φ γ'' ∧ γ'' ^ 2 = ∏ i, (s.β i) ^ ((e i : ℕ)) := by
    rcases mul_self_eq_mul_self_iff.mp hww with h | h
    · exact ⟨γ, h, hγ⟩
    · exact ⟨-γ, by rw [h, map_neg], by rw [neg_sq]; exact hγ⟩
  have hγ''ne : γ'' ≠ 0 := by
    intro h0
    have h2 := hγ''sq
    rw [h0] at h2
    have h3 : (∏ i, (s.β i) ^ ((e i : ℕ))) = 0 := by rw [← h2]; ring
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hs.beta_ne i)) h3
  -- the `k`-th column
  have ht_spec' : ∀ a, ((m' a k : ℤ) : ℂ) = (A a : ℂ) - (2:ℂ)^(s.v+1) * (t a : ℂ) := by
    intro a
    have h := ht_spec a
    have h5 : (((2:ℤ)^(s.v+1) * t a : ℤ) : ℂ) = ((A a : ℤ) : ℂ) - ((m' a k : ℤ) : ℂ) := by
      rw [h, Int.cast_sub]
    have h7 : ((A a : ℤ) : ℂ) - ((m' a k : ℤ) : ℂ) = ((2:ℤ)^(s.v+1) : ℂ) * (t a : ℂ) := by
      rw [← h5]
      push_cast
      ring
    have h6 : ((m' a k : ℤ) : ℂ) = ((A a : ℤ) : ℂ) - ((2:ℤ)^(s.v+1) : ℂ) * (t a : ℂ) := by
      rw [← h7]
      ring
    rw [h6]
    push_cast
    ring
  have hkcol : Complex.exp (((2:ℂ)^(s.v+1))⁻¹ * ∑ a, (m' a k : ℂ) * L a)
      = φ (γ'' * ∏ a, (α a) ^ (-(t a))) := by
    have hsplit : ∑ a, (m' a k : ℂ) * L a
        = ∑ a, (A a : ℂ) * L a - (2:ℂ)^(s.v+1) * ∑ a, (t a : ℂ) * L a := by
      rw [show (∑ a, (A a : ℂ) * L a - (2:ℂ)^(s.v+1) * ∑ a, (t a : ℂ) * L a)
          = ∑ a, ((A a : ℂ) * L a - (2:ℂ)^(s.v+1) * ((t a : ℂ) * L a)) by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ht_spec' a]; ring
    have hexp1 : Complex.exp (((2:ℂ)^(s.v+1))⁻¹ * (∑ a, (A a : ℂ) * L a
        - (2:ℂ)^(s.v+1) * ∑ a, (t a : ℂ) * L a))
        = w * Complex.exp (-(∑ a, (t a : ℂ) * L a)) := by
      rw [hwdef, ← Complex.exp_add]
      congr 1
      have hne : ((2:ℂ)^(s.v+1)) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      ring
    have hexp2 : Complex.exp (-(∑ a, (t a : ℂ) * L a)) = φ (∏ a, (α a) ^ (-(t a))) := by
      rw [← Finset.sum_neg_distrib, Complex.exp_sum, map_prod]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [map_zpow₀]
      have h1 : -((t a : ℂ) * L a) = ((-(t a) : ℤ) : ℂ) * L a := by push_cast; ring
      rw [h1, Complex.exp_int_mul]
      congr 1
      rw [hLdef]
      exact Complex.exp_log (by rw [← map_zero φ]; exact φ.injective.ne (hα a))
    rw [hsplit, hexp1, hexp2, hwγ'', ← map_mul]
  -- assemble
  set β' : Fin n → K := fun j => if j = k then γ'' * ∏ a, (α a) ^ (-(t a)) else s.β j with hβ'def
  set nu' : Fin n → ℕ := fun j => if j = k then s.nu k + 1 else s.nu j with hnu'def
  refine ⟨⟨s.v + 1, nu', m', β'⟩, ?_, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show β' j ≠ 0
    rw [hβ'def]
    by_cases hjk : j = k
    · simp only [hjk, if_true]
      exact mul_ne_zero hγ''ne (Finset.prod_ne_zero_iff.mpr fun a _ => zpow_ne_zero _ (hα a))
    · simp only [hjk, if_false]
      exact hs.beta_ne j
  · show ∑ j, nu' j = s.v + 1
    rw [hnu'def]
    have h1 : ∀ j : Fin n, (if j = k then s.nu k + 1 else s.nu j)
        = s.nu j + (if j = k then 1 else 0) := by
      intro j; by_cases h : j = k <;> simp [h]
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib]
    have h2 : (∑ j, if j = k then (1:ℕ) else 0) = 1 := by
      rw [Finset.sum_ite_eq' Finset.univ k (fun _ => (1:ℕ))]; simp
    rw [h2, hs.sum_nu]
  · intro i j hij
    show m' i j = 0
    by_cases hjk : j = k
    · have hki : k < i := by rwa [hjk] at hij
      rw [hjk]
      exact hr_zero i hki
    · rw [hm'def]
      simp only [if_neg hjk]
      rw [hs.tri i j hij, mul_zero]
  · intro j
    show m' j j = (2:ℤ) ^ (s.v + 1 - nu' j)
    by_cases hjk : j = k
    · rw [hjk]
      have hnuk : nu' k = s.nu k + 1 := by rw [hnu'def]; simp
      have hmk : m' k k = s.m k k := by
        simp only [hm'def, if_true]
        exact hA_k
      have hexp : s.v + 1 - nu' k = s.v - s.nu k := by rw [hnuk]; omega
      rw [hmk, hs.diag k, hexp]
    · have hmj : m' j j = 2 * s.m j j := by
        simp only [hm'def, if_neg hjk]
      have hnuj : nu' j = s.nu j := by rw [hnu'def]; simp [hjk]
      have hexp : s.v + 1 - s.nu j = (s.v - s.nu j) + 1 := by have := hs.nu_le j; omega
      rw [hmj, hs.diag j, hnuj, hexp, pow_succ']
  · intro j
    show Complex.exp (((2:ℂ)^(s.v+1))⁻¹ * ∑ i, (m' i j : ℂ) * Complex.log (φ (α i))) = φ (β' j)
    by_cases hjk : j = k
    · rw [hjk]
      rw [hβ'def]; simp only [if_true]
      have hsum : ∑ i, (m' i k : ℂ) * Complex.log (φ (α i)) = ∑ a, (m' a k : ℂ) * L a := by
        simp only [hLdef]
      rw [hsum, hkcol]
    · rw [hβ'def]; simp only [hjk, if_false]
      have hsum : ∑ i, (m' i j : ℂ) * Complex.log (φ (α i))
          = 2 * (∑ i, (s.m i j : ℂ) * Complex.log (φ (α i))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [hm'def, if_neg hjk]
        push_cast
        ring
      rw [hsum]
      have h2 : ((2:ℂ)^(s.v+1))⁻¹ * (2 * ∑ i, (s.m i j : ℂ) * Complex.log (φ (α i)))
          = ((2:ℂ)^s.v)⁻¹ * ∑ i, (s.m i j : ℂ) * Complex.log (φ (α i)) := by
        have hne : ((2:ℂ)^s.v) ≠ 0 := pow_ne_zero _ (by norm_num)
        rw [pow_succ]
        field_simp
      rw [h2]
      exact hs.exp_eq j
  · intro j
    show (∑ i, |(m' i j : ℝ)| * hp φ (α i)) ≤ (2:ℝ)^(s.v+1) * sig φ α j
    by_cases hjk : j = k
    · rw [hjk]
      have hb : ∀ a : Fin n, |(m' a k : ℝ)| * hp φ (α a) ≤ (2:ℝ)^s.v * hp φ (α k) := by
        intro a
        by_cases hak : k < a
        · rw [hr_zero a hak]
          simp only [Int.cast_zero, abs_zero, zero_mul]
          exact mul_nonneg (by positivity) (le_of_lt (hp_pos φ (α k)))
        · have ha : a ≤ k := not_lt.mp hak
          have h1 : |(m' a k : ℝ)| ≤ (2:ℝ)^s.v := by
            by_cases haek : a = k
            · rw [haek]
              have hmk : m' k k = s.m k k := by
                simp only [hm'def, if_true]; exact hA_k
              have hle : s.v - s.nu k ≤ s.v := by have := hs.nu_le k; omega
              rw [hmk, hs.diag k]
              push_cast
              rw [abs_of_nonneg (by positivity)]
              exact pow_le_pow_right₀ (by norm_num) hle
            · have hm : m' a k = r a := by simp only [hm'def, if_true, if_neg haek]
              rw [hm]
              exact_mod_cast (hr' a).2
          calc |(m' a k : ℝ)| * hp φ (α a) ≤ (2:ℝ)^s.v * hp φ (α a) :=
                mul_le_mul_of_nonneg_right h1 (le_of_lt (hp_pos φ (α a)))
            _ ≤ (2:ℝ)^s.v * hp φ (α k) :=
                mul_le_mul_of_nonneg_left (hsort a k ha) (by positivity)
      have hsum_eq : ∑ a, |(m' a k : ℝ)| * hp φ (α a)
          = ∑ a ∈ Finset.univ.filter (fun a : Fin n => a ≤ k),
              |(m' a k : ℝ)| * hp φ (α a) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin n => a ≤ k)]
        have hz : (∑ a ∈ Finset.univ.filter (fun a : Fin n => ¬ (a ≤ k)),
            |(m' a k : ℝ)| * hp φ (α a)) = 0 := by
          refine Finset.sum_eq_zero fun a ha => ?_
          have hna : ¬ (a ≤ k) := (Finset.mem_filter.mp ha).2
          rw [hr_zero a (not_le.mp hna)]; simp
        rw [hz, add_zero]
      rw [hsum_eq]
      calc ∑ a ∈ Finset.univ.filter (fun a : Fin n => a ≤ k), |(m' a k : ℝ)| * hp φ (α a)
          ≤ (Finset.univ.filter (fun a : Fin n => a ≤ k)).card • ((2:ℝ)^s.v * hp φ (α k)) :=
            Finset.sum_le_card_nsmul _ _ _ (fun a _ => hb a)
        _ = (((k : ℕ) : ℝ) + 1) * ((2:ℝ)^s.v * hp φ (α k)) := by
            rw [card_filter_le k, nsmul_eq_mul]; norm_num
        _ ≤ (2:ℝ)^(s.v+1) * sig φ α k := by
            have h2 : (((k : ℕ) : ℝ) + 1) * hp φ (α k) ≤ 2 * sig φ α k := by
              have h3 := half_mul_hp_le_sig φ α k
              have h4 := hp_pos φ (α k)
              rw [sig] at h3 ⊢
              have : (((k : ℕ) : ℝ)) = ((k : ℝ)) := by simp
              rw [this] at h3 ⊢
              nlinarith [h3, h4]
            have h5 : (0:ℝ) < (2:ℝ)^s.v := by positivity
            rw [pow_succ]
            nlinarith [h2, h5]
    · have hmj : ∀ a, m' a j = 2 * s.m a j := by
        intro a; simp only [hm'def, if_neg hjk]
      have hsum : ∑ a, |(m' a j : ℝ)| * hp φ (α a)
          = 2 * ∑ a, |(s.m a j : ℝ)| * hp φ (α a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hmj' : (m' a j : ℝ) = 2 * (s.m a j : ℝ) := by
          rw [hmj a]; push_cast; ring
        rw [hmj', abs_mul, abs_two]
        ring
      rw [hsum]
      calc 2 * ∑ a, |(s.m a j : ℝ)| * hp φ (α a) ≤ 2 * ((2:ℝ)^s.v * sig φ α j) := by
            linarith [hs.colsum j]
        _ = (2:ℝ)^(s.v+1) * sig φ α j := by rw [pow_succ]; ring

end Work.BW
