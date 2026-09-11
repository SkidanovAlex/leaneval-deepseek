import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Multi

/-!
# Task file: prove `Submission.Multi.mass_sum_eq_pow` (and its corollaries).
Definitions live in Submission/Multi.lean (namespace Submission.Multi):
`msizeExact M` = Finset of multisets `m : X → ℕ` with `sizeM m = M`,
`mass M μ m := (Nat.factorial M : ℝ) * ∏ x : X, μ x ^ m x / Nat.factorial (m x)`,
`sizeM m := ∑ x, m x`.  This file proves the multinomial mass expansion
  ∑_{m ∈ msizeExact M} mass M μ m = (∑ x, μ x)^M
by induction on M (base: only the zero multiset; step: reindex (y, m) ↦ (addOne m y, y)
bijectively between `univ × msizeExact M` and pairs (m', y) with m' of size M+1 and 1 ≤ m' y,
using the coordinate identity `mass_erase_mul`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

variable {X : Type*} [Fintype X]

noncomputable def addOne (m : X → ℕ) (y : X) : X → ℕ :=
  fun x => if x = y then m x + 1 else m x

lemma sizeM_addOne (m : X → ℕ) (y : X) : sizeM (addOne m y) = sizeM m + 1 := by
  classical
  unfold sizeM addOne
  rw [sum_univ_singleton_add (fun x : X => if x = y then m x + 1 else m x) y]
  rw [sum_univ_singleton_add (fun x : X => m x) y]
  simp
  have hsum : (∑ x ∈ (Finset.univ.erase y), (if x = y then m x + 1 else m x)) =
      ∑ x ∈ (Finset.univ.erase y), m x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxne : x ≠ y := (Finset.mem_erase.mp hx).1
    simp [hxne]
  rw [hsum]
  omega

lemma addOne_eraseOne (m : X → ℕ) (y : X) : eraseOne (addOne m y) y = m := by
  funext x
  by_cases hxy : x = y
  · subst x
    simp [addOne, eraseOne]
  · simp [addOne, eraseOne, hxy]

lemma eraseOne_addOne {m : X → ℕ} (y : X) (hm : 1 ≤ m y) : addOne (eraseOne m y) y = m := by
  funext x
  by_cases hxy : x = y
  · subst x
    simp [addOne, eraseOne, Nat.sub_add_cancel hm]
  · simp [addOne, eraseOne, hxy]

/-- product over X split at coordinate y -/
lemma prod_split (f : X → ℝ) (y : X) :
    (∏ x : X, f x) = f y * (∏ x ∈ (Finset.univ.erase y), f x) := by
  classical
  exact (Finset.mul_prod_erase (Finset.univ : Finset X) f (Finset.mem_univ y)).symm

/-- coordinate identity: absorbing the extra factor -/
lemma coord_abs (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    a * (a ^ (n - 1) / Nat.factorial (n - 1)) = (a ^ n / Nat.factorial n) * (n : ℝ) := by
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hfac_nat : Nat.factorial n = n * Nat.factorial (n - 1) := by
    calc
      Nat.factorial n = Nat.factorial (n - 1 + 1) := by rw [hn']
      _ = (n - 1 + 1) * Nat.factorial (n - 1) := by rw [Nat.factorial_succ]
      _ = n * Nat.factorial (n - 1) := by rw [hn']
  have hfac : (Nat.factorial n : ℝ) = (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast hfac_nat
  have hpow : a * a ^ (n - 1) = a ^ n := by
    rw [← pow_succ', hn']
  -- hmm test hpow direction: a·a^{n-1} = a^n: pow_succ' (a)(n-1): a^{n-1+1} = a·a^{n-1}:
  -- rw [← pow_succ'] gives a^{(n-1)+1} = a^n then rw [hn'] gives a^n = a^n
  calc
    a * (a ^ (n - 1) / Nat.factorial (n - 1))
        = (a * a ^ (n - 1)) / Nat.factorial (n - 1) := by ring
    _ = a ^ n / Nat.factorial (n - 1) := by rw [hpow]
    _ = (a ^ n / Nat.factorial n) * (n : ℝ) := by
          have hdn : (n : ℝ) ≠ 0 := by
            have : n ≠ 0 := by omega
            exact_mod_cast this
          have hd1 : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos (n - 1)))
          field_simp [hdn, hd1]
          rw [hfac]
          ring

/-- products: erasing y makes coordinate y smaller -/
lemma prod_erase (μ : X → ℝ) (m : X → ℕ) (y : X) (hm : 1 ≤ m y) :
    μ y * (∏ x : X, μ x ^ eraseOne m y x / Nat.factorial (eraseOne m y x)) =
      (∏ x : X, μ x ^ m x / Nat.factorial (m x)) * (m y : ℝ) := by
  classical
  let P : ℝ := ∏ x ∈ (Finset.univ.erase y), μ x ^ m x / Nat.factorial (m x)
  have hg : (∏ x : X, μ x ^ eraseOne m y x / Nat.factorial (eraseOne m y x)) =
      (μ y ^ (m y - 1) / Nat.factorial (m y - 1)) * P := by
    rw [prod_split (fun x : X => μ x ^ eraseOne m y x / Nat.factorial (eraseOne m y x)) y]
    have hy1 : μ y ^ eraseOne m y y / Nat.factorial (eraseOne m y y) =
        μ y ^ (m y - 1) / Nat.factorial (m y - 1) := by
      simp [eraseOne]
    have hy2 : (∏ x ∈ (Finset.univ.erase y), μ x ^ eraseOne m y x / Nat.factorial (eraseOne m y x)) = P := by
      dsimp [P]
      apply Finset.prod_congr rfl
      intro x hx
      have hxne : x ≠ y := (Finset.mem_erase.mp hx).1
      simp [eraseOne, hxne]
    rw [hy1, hy2]
  have hf : (∏ x : X, μ x ^ m x / Nat.factorial (m x)) = (μ y ^ m y / Nat.factorial (m y)) * P := by
    rw [prod_split (fun x : X => μ x ^ m x / Nat.factorial (m x)) y]
  calc
    μ y * (∏ x : X, μ x ^ eraseOne m y x / Nat.factorial (eraseOne m y x))
        = μ y * ((μ y ^ (m y - 1) / Nat.factorial (m y - 1)) * P) := by rw [hg]
    _ = (μ y * (μ y ^ (m y - 1) / Nat.factorial (m y - 1))) * P := by ring
    _ = ((μ y ^ m y / Nat.factorial (m y)) * (m y : ℝ)) * P := by rw [coord_abs (μ y) (m y) hm]
    _ = ((μ y ^ m y / Nat.factorial (m y)) * P) * (m y : ℝ) := by ring
    _ = (∏ x : X, μ x ^ m x / Nat.factorial (m x)) * (m y : ℝ) := by rw [← hf]

/-- the mass relation when deleting one copy of y -/
lemma mass_erase_mul (M : ℕ) (μ : X → ℝ) (m : X → ℕ) (y : X) (hm : 1 ≤ m y) :
    μ y * mass M μ (eraseOne m y) = mass (M + 1) μ m * (m y : ℝ) / ((M + 1 : ℕ) : ℝ) := by
  classical
  have hden : ((M + 1 : ℕ) : ℝ) ≠ 0 := by
    have : M + 1 ≠ 0 := Nat.succ_ne_zero M
    exact_mod_cast this
  have hmul : μ y * mass M μ (eraseOne m y) * ((M + 1 : ℕ) : ℝ) = mass (M + 1) μ m * (m y : ℝ) := by
    have hfac : (Nat.factorial (M + 1) : ℝ) = (Nat.factorial M : ℝ) * ((M + 1 : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      ring
    unfold mass
    calc
      μ y * ((Nat.factorial M : ℝ) * (∏ x : X, μ x ^ eraseOne m y x / Nat.factorial (eraseOne m y x))) * ((M + 1 : ℕ) : ℝ)
          = (Nat.factorial M : ℝ) * ((M + 1 : ℕ) : ℝ) * (μ y * (∏ x : X, μ x ^ eraseOne m y x / Nat.factorial (eraseOne m y x))) := by ring
      _ = (Nat.factorial (M + 1) : ℝ) * ((∏ x : X, μ x ^ m x / Nat.factorial (m x)) * (m y : ℝ)) := by
            rw [← hfac]
            rw [prod_erase μ m y hm]
      _ = (Nat.factorial (M + 1) : ℝ) * (∏ x : X, μ x ^ m x / Nat.factorial (m x)) * (m y : ℝ) := by ring
  calc
    μ y * mass M μ (eraseOne m y)
        = (μ y * mass M μ (eraseOne m y)) * ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) := by
            field_simp [hden]
    _ = mass (M + 1) μ m * (m y : ℝ) / ((M + 1 : ℕ) : ℝ) := by rw [hmul]

/-- inner sum over the support-multiplicity equals the (M+1)-mass -/
lemma inner_mass_sum {M : ℕ} (μ : X → ℝ) (m' : X → ℕ) (hm' : m' ∈ msizeExact (X := X) (M + 1)) :
    (∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ m' y)), μ y * mass M μ (eraseOne m' y))
      = mass (M + 1) μ m' := by
  classical
  let F : Finset X := Finset.univ.filter (fun y : X => 1 ≤ m' y)
  have hsize : sizeM m' = M + 1 := (mem_msizeExact_iff (X := X) (M := M + 1)).mp hm'
  have hsumN : (∑ y ∈ F, m' y) = M + 1 := by
    dsimp [F]
    calc
      (∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ m' y)), m' y)
          = ∑ y : X, m' y := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro y hy
            by_cases h : 1 ≤ m' y
            · simp [h]
            · have hz : m' y = 0 := by omega
              simp [hz]
      _ = M + 1 := by
            rw [← hsize]
            rfl
  have hden : ((M + 1 : ℕ) : ℝ) ≠ 0 := by
    have : M + 1 ≠ 0 := Nat.succ_ne_zero M
    exact_mod_cast this
  have hdiv : (∑ y ∈ F, (m' y : ℝ) / ((M + 1 : ℕ) : ℝ)) = 1 := by
    calc
      (∑ y ∈ F, (m' y : ℝ) / ((M + 1 : ℕ) : ℝ))
          = (∑ y ∈ F, (m' y : ℝ)) / ((M + 1 : ℕ) : ℝ) := by
              rw [← Finset.sum_div]
      _ = ((∑ y ∈ F, m' y : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_sum]
      _ = 1 := by
              rw [hsumN]
              exact div_self hden
  have hfac : (∑ y ∈ F, mass (M + 1) μ m' * (m' y : ℝ) / ((M + 1 : ℕ) : ℝ))
      = mass (M + 1) μ m' * (∑ y ∈ F, (m' y : ℝ) / ((M + 1 : ℕ) : ℝ)) := by
    calc
      (∑ y ∈ F, mass (M + 1) μ m' * (m' y : ℝ) / ((M + 1 : ℕ) : ℝ))
          = ∑ y ∈ F, mass (M + 1) μ m' * ((m' y : ℝ) / ((M + 1 : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
      _ = mass (M + 1) μ m' * (∑ y ∈ F, (m' y : ℝ) / ((M + 1 : ℕ) : ℝ)) := by
            rw [← Finset.mul_sum]
  calc
    (∑ y ∈ F, μ y * mass M μ (eraseOne m' y))
        = (∑ y ∈ F, mass (M + 1) μ m' * (m' y : ℝ) / ((M + 1 : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact mass_erase_mul M μ m' y ((Finset.mem_filter.mp hy).2)
    _ = mass (M + 1) μ m' * (∑ y ∈ F, (m' y : ℝ) / ((M + 1 : ℕ) : ℝ)) := hfac
    _ = mass (M + 1) μ m' * 1 := by rw [hdiv]
    _ = mass (M + 1) μ m' := by ring

/-- double-sum reindexing: (y, m) ↦ (addOne m y, y) -/
lemma sum_bij_msizeExact (M : ℕ) (F : X → (X → ℕ) → ℝ) (G : (X → ℕ) → X → ℝ)
    (h : ∀ (y : X) (m : X → ℕ), G (addOne m y) y = F y m) :
    (∑ y : X, ∑ m ∈ msizeExact (X := X) M, F y m) =
      (∑ m' ∈ msizeExact (X := X) (M + 1),
        ∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ m' y)), G m' y) := by
  classical
  let S : Finset (X × (X → ℕ)) := (Finset.univ : Finset X).product (msizeExact (X := X) M)
  let T : Finset (Sigma (fun _ : X → ℕ => X)) :=
    (msizeExact (X := X) (M + 1)).sigma
      (fun m' : X → ℕ => (Finset.univ.filter (fun y : X => 1 ≤ m' y)))
  have hST : (∑ p ∈ S, F p.1 p.2) = ∑ q ∈ T, G q.1 q.2 := by
    refine Finset.sum_bij (fun p hp => (⟨addOne p.2 p.1, p.1⟩ : Sigma (fun _ : X → ℕ => X))) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_sigma]
      constructor
      · have hs : sizeM p.2 = M := (mem_msizeExact_iff (X := X) (M := M)).mp (Finset.mem_product.mp hp).2
        apply mem_msizeExact
        change sizeM (addOne p.2 p.1) = M + 1
        rw [sizeM_addOne]
        omega
      · rw [Finset.mem_filter]
        constructor
        · simp
        · have h11 : addOne p.2 p.1 p.1 = p.2 p.1 + 1 := by
            unfold addOne
            rw [if_pos rfl]
          change 1 ≤ addOne p.2 p.1 p.1
          rw [h11]
          omega
    · intro p1 hp1 p2 hp2 heq
      apply Prod.ext
      · have hsnd' : p1.1 = p2.1 := by simpa using congrArg Sigma.snd heq
        exact hsnd'
      · have hfst' : addOne p1.2 p1.1 = addOne p2.2 p2.1 := by simpa using congrArg Sigma.fst heq
        calc
          p1.2 = eraseOne (addOne p1.2 p1.1) p1.1 := (addOne_eraseOne p1.2 p1.1).symm
          _ = eraseOne (addOne p2.2 p2.1) p1.1 := by rw [hfst']
          _ = eraseOne (addOne p2.2 p2.1) p2.1 := by
                have hsnd' : p1.1 = p2.1 := by simpa using congrArg Sigma.snd heq
                rw [hsnd']
          _ = p2.2 := addOne_eraseOne p2.2 p2.1
    · intro b hb
      rcases b with ⟨m', y⟩
      have hms : m' ∈ msizeExact (X := X) (M + 1) := (Finset.mem_sigma.mp hb).1
      have hfy : y ∈ (Finset.univ.filter (fun y : X => 1 ≤ m' y)) := (Finset.mem_sigma.mp hb).2
      have hmy : 1 ≤ m' y := (Finset.mem_filter.mp hfy).2
      refine ⟨(y, eraseOne m' y), ?_, ?_⟩
      · dsimp [S]
        rw [Finset.mem_product]
        constructor
        · simp
        · change eraseOne m' y ∈ msizeExact (X := X) M
          apply mem_msizeExact
          have hsz : sizeM m' = M + 1 := (mem_msizeExact_iff (X := X) (M := M + 1)).mp hms
          have hsz2 : sizeM (eraseOne m' y) + 1 = sizeM m' := sizeM_eraseOne_add m' y (by omega)
          omega
      · have hmain : addOne (eraseOne m' y) y = m' := eraseOne_addOne (m := m') y hmy
        rw [hmain]
    · intro p hp
      dsimp
      exact (h p.1 p.2).symm
  calc
    (∑ y : X, ∑ m ∈ msizeExact (X := X) M, F y m)
        = (∑ p ∈ S, F p.1 p.2) := by
            dsimp [S]
            rw [Finset.sum_product]
    _ = (∑ q ∈ T, G q.1 q.2) := hST
    _ = (∑ m' ∈ msizeExact (X := X) (M + 1),
            ∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ m' y)), G m' y) := by
            dsimp [T]
            rw [Finset.sum_sigma]

/-- multinomial mass expansion -/
lemma mass_sum_eq_pow (M : ℕ) (μ : X → ℝ) :
    (∑ m ∈ msizeExact (X := X) M, mass (X := X) M μ m) = (∑ x : X, μ x) ^ M := by
  classical
  induction M with
  | zero =>
      have hz : msizeExact (X := X) 0 = ({fun _ : X => 0} : Finset (X → ℕ)) := by
        classical
        ext m
        rw [mem_msizeExact_iff (X := X) (m := m) (M := 0)]
        constructor
        · intro hm
          exact (Finset.mem_singleton).mpr (by
            funext x
            have hle : m x ≤ sizeM m :=
              Finset.single_le_sum (by intro y hy; exact Nat.zero_le _) (Finset.mem_univ x)
            omega)
        · intro hm
          have hEq : m = (fun _ : X => 0) := Finset.mem_singleton.mp hm
          rw [hEq]
          simp [sizeM]
      rw [hz]
      simp [mass]
  | succ M ih =>
      calc
        (∑ m ∈ msizeExact (X := X) (M + 1), mass (X := X) (M + 1) μ m)
            = (∑ m' ∈ msizeExact (X := X) (M + 1),
                ∑ y ∈ (Finset.univ.filter (fun y : X => 1 ≤ m' y)),
                  μ y * mass (X := X) M μ (eraseOne m' y)) := by
                apply Finset.sum_congr rfl
                intro m' hm'
                exact (inner_mass_sum (M := M) μ m' hm').symm
        _ = (∑ y : X, ∑ m ∈ msizeExact (X := X) M, μ y * mass (X := X) M μ m) := by
                exact (sum_bij_msizeExact (M := M)
                  (F := fun y m => μ y * mass (X := X) M μ m)
                  (G := fun m' y => μ y * mass (X := X) M μ (eraseOne m' y))
                  (fun y m => by simp [addOne_eraseOne])).symm
        _ = (∑ x : X, μ x) * (∑ m ∈ msizeExact (X := X) M, mass (X := X) M μ m) := by
                calc
                  (∑ y : X, ∑ m ∈ msizeExact (X := X) M, μ y * mass (X := X) M μ m)
                      = ∑ y : X, μ y * (∑ m ∈ msizeExact (X := X) M, mass (X := X) M μ m) := by
                          apply Finset.sum_congr rfl
                          intro y hy
                          rw [← Finset.mul_sum]
                  _ = (∑ x : X, μ x) * (∑ m ∈ msizeExact (X := X) M, mass (X := X) M μ m) := by
                          rw [← Finset.sum_mul]
        _ = (∑ x : X, μ x) * (∑ x : X, μ x) ^ M := by rw [ih]
        _ = (∑ x : X, μ x) ^ (M + 1) := by
                rw [mul_comm, pow_succ]

/-- sum of masses ≤ 1 -/
lemma mass_sum_le_one {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hsum : (∑ x, μ x) ≤ 1) (M : ℕ) :
    (∑ m ∈ msizeExact (X := X) M, mass (X := X) M μ m) ≤ 1 := by
  rw [mass_sum_eq_pow]
  exact pow_le_one₀ (Finset.sum_nonneg (by intro x hx; exact hμ x)) hsum

/-- each mass is nonnegative -/
lemma mass_nonneg' {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (M : ℕ) (m : X → ℕ) : 0 ≤ mass M μ m := by
  exact mass_nonneg M hμ m


/-- the multiplicity-boosting constant K of Theorem multi'-w -/
noncomputable def Kbig : ℕ := 10 ^ 70

/-- e := Euler's number -/
noncomputable def ee : ℝ := Real.exp 1

/-- eN := e·N -/
noncomputable def eN (N : ℕ) : ℝ := ee * (N : ℝ)


end Multi
end Submission
