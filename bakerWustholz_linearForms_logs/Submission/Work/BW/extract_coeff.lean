import Mathlib
import Submission.Work.BW.wuestholzDefs
import Submission.Work.BW.extract_defs
import Submission.Work.BW.gamma_rule
import Submission.Work.BW.mainterm_cons
import Submission.Work.BW.wordof_facts
import Submission.Work.BW.applyl_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

variable {R : Type*} [CommRing R] {ℓ : ℕ}

/-- Additivity of `applyWord` over a finite sum. -/
lemma applyWord_sum (Λ : Fin ℓ → R → R) (hadd : ∀ i x y, Λ i (x + y) = Λ i x + Λ i y)
    {ι : Type*} (s : Finset ι) (f : ι → R) (w : List (Fin ℓ)) :
    applyWord Λ w (∑ i ∈ s, f i) = ∑ i ∈ s, applyWord Λ w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact applyWord_zero Λ hadd w
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, applyWord_add Λ hadd, ih]

/-- The expected main term in closed form when the word is `wordOf α`. -/
lemma mainTerm_wordOf (u D : Fin ℓ → R) (α β : Fin ℓ → ℕ) :
    mainTerm u D (wordOf α) β
      = (∏ i, ((β i).descFactorial (α i) : R)) * (∏ i, D i ^ (α i)) *
          (∏ i, u i ^ (β i - α i)) := by
  simp only [mainTerm, (wordof_facts α).1]

/-- The monomial invariant: applying the word `w` of derivations to `c · ∏ i, u i ^ β i` agrees
with `c · mainTerm w β` up to the filtration `J_{∑β + 1 - |w|}`. -/
theorem word_inv (Λ : Fin ℓ → R → R) (u D : Fin ℓ → R) (𝔎 : Ideal R)
    (hadd : ∀ i x y, Λ i (x + y) = Λ i x + Λ i y)
    (hleib : ∀ i x y, Λ i (x * y) = Λ i x * y + x * Λ i y)
    (hcong : ∀ i j, Λ i (u j) - D j * (if i = j then (1 : R) else 0) ∈ 𝔎)
    (w : List (Fin ℓ)) (c : R) (β : Fin ℓ → ℕ) :
    applyWord Λ w (c * ∏ i, u i ^ β i) - c * mainTerm u D w β
      ∈ Jfilt 𝔎 u (Jidx β w.length) := by
  induction w generalizing c β with
  | nil =>
      rw [applyWord_nil, mainTerm_nil, sub_self]
      exact Ideal.zero_mem _
  | cons i w' ih =>
      have hstep : applyWord Λ (i :: w') (c * ∏ j, u j ^ β j)
          = applyWord Λ w' ((Λ i c) * (∏ j, u j ^ β j))
            + applyWord Λ w' ((c * (β i : R) * D i) * (∏ l, u l ^ decr β i l))
            + ∑ j, applyWord Λ w' ((c * ((β j : R) *
                (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                  (∏ l, u l ^ decr β j l)) := by
        have hraw : applyWord Λ (i :: w') (c * ∏ j, u j ^ β j)
            = applyWord Λ w' ((Λ i c) * (∏ j, u j ^ β j))
              + applyWord Λ w' (c * ((β i : R) * D i * (∏ l, u l ^ decr β i l)))
              + ∑ j, applyWord Λ w' (c * ((∏ l, u l ^ decr β j l) * ((β j : R) *
                  (Λ i (u j) - D j * (if i = j then (1 : R) else 0))))) := by
          rw [applyWord_cons, hleib i c (∏ j, u j ^ β j),
              gamma_rule 𝔎 Λ u D hadd hleib hcong i β, mul_add, Finset.mul_sum,
              applyWord_add Λ hadd, applyWord_add Λ hadd, applyWord_sum Λ hadd, ← add_assoc]
        have hb : applyWord Λ w' (c * ((β i : R) * D i * (∏ l, u l ^ decr β i l)))
            = applyWord Λ w' ((c * (β i : R) * D i) * (∏ l, u l ^ decr β i l)) := by
          congr 1; ring
        have hs : (∑ j, applyWord Λ w' (c * ((∏ l, u l ^ decr β j l) * ((β j : R) *
              (Λ i (u j) - D j * (if i = j then (1 : R) else 0))))))
            = ∑ j, applyWord Λ w' ((c * ((β j : R) *
                (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                  (∏ l, u l ^ decr β j l)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); congr 1; ring
        rw [hraw, hb, hs]
      rw [hstep]
      -- memberships
      have hJt : Jfilt 𝔎 u (Jidx β (w'.length + 1))
          = Jfilt 𝔎 u (Jidx β (i :: w').length) := rfl
      have hkeyA : Jfilt 𝔎 u (Jidx β w'.length) ≤ Jfilt 𝔎 u (Jidx β (w'.length + 1)) :=
        Jfilt_antitone (by simp only [Jidx]; omega)
      have hkeyB : Jfilt 𝔎 u (Jidx (decr β i) w'.length)
          ≤ Jfilt 𝔎 u (Jidx β (w'.length + 1)) :=
        Jfilt_antitone (by
          have h := sum_le_sum_decr_add_one β i
          simp only [Jidx]; omega)
      have hA : applyWord Λ w' ((Λ i c) * ∏ j, u j ^ β j) - (Λ i c) * mainTerm u D w' β
          ∈ Jfilt 𝔎 u (Jidx β (w'.length + 1)) := hkeyA (ih (Λ i c) β)
      have hB : applyWord Λ w' ((c * (β i : R) * D i) * (∏ l, u l ^ decr β i l))
            - (c * (β i : R) * D i) * mainTerm u D w' (decr β i)
          ∈ Jfilt 𝔎 u (Jidx β (w'.length + 1)) := hkeyB (ih (c * (β i : R) * D i) (decr β i))
      have hC : ∀ j, applyWord Λ w' ((c * ((β j : R) *
              (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                (∏ l, u l ^ decr β j l))
            - (c * ((β j : R) * (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                mainTerm u D w' (decr β j)
          ∈ Jfilt 𝔎 u (Jidx β (w'.length + 1)) := by
        intro j
        refine (Jfilt_antitone (by
          have h := sum_le_sum_decr_add_one β j
          simp only [Jidx]; omega)) (ih (c * ((β j : R) *
            (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) (decr β j))
      -- main part memberships
      have hM1 : (Λ i c) * mainTerm u D w' β ∈ Jfilt 𝔎 u (Jidx β (w'.length + 1)) := by
        have hle : Jidx β (w'.length + 1) ≤ mainDeg w' β := by
          have h := sum_le_mainDeg_add w' β
          simp only [Jidx]; omega
        exact (pow_le_Jfilt (𝔎 := 𝔎) (u := u) _)
          (Ideal.mul_mem_left _ _ ((Ideal.pow_le_pow_right hle) (mainTerm_mem w' β)))
      have hM3 : ∀ j, (c * ((β j : R) * (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
            mainTerm u D w' (decr β j) ∈ Jfilt 𝔎 u (Jidx β (w'.length + 1)) := by
        intro j
        have hK : (c * ((β j : R) * (Λ i (u j) - D j * (if i = j then (1 : R) else 0))))
            ∈ 𝔎 := Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hcong i j))
        have hle : Jidx β (w'.length + 1) - 1 ≤ mainDeg w' (decr β j) := by
          have h := sum_decr_le_mainDeg_add w' β j
          have h2 := sum_le_sum_decr_add_one β j
          simp only [Jidx]; omega
        have hmem := (Ideal.pow_le_pow_right hle) (mainTerm_mem (u := u) (D := D) w' (decr β j))
        have hmul : (c * ((β j : R) * (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
            mainTerm u D w' (decr β j) ∈ 𝔎 * Uspan u ^ (Jidx β (w'.length + 1) - 1) :=
          Ideal.mul_mem_mul hK hmem
        exact (mul_pow_le_Jfilt_succ (𝔎 := 𝔎) (u := u) (Jidx β (w'.length + 1) - 1)).trans
          (Jfilt_antitone (by omega)) hmul
      -- assembly
      have h1 : applyWord Λ w' ((Λ i c) * ∏ j, u j ^ β j)
            + applyWord Λ w' ((c * (β i : R) * D i) * (∏ l, u l ^ decr β i l))
            + (∑ j, applyWord Λ w' ((c * ((β j : R) *
                (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                  (∏ l, u l ^ decr β j l)))
            - ((Λ i c) * mainTerm u D w' β
               + (c * (β i : R) * D i) * mainTerm u D w' (decr β i)
               + ∑ j, (c * ((β j : R) *
                   (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                     mainTerm u D w' (decr β j))
          ∈ Jfilt 𝔎 u (Jidx β (w'.length + 1)) := by
        have heq : applyWord Λ w' ((Λ i c) * ∏ j, u j ^ β j)
              + applyWord Λ w' ((c * (β i : R) * D i) * (∏ l, u l ^ decr β i l))
              + (∑ j, applyWord Λ w' ((c * ((β j : R) *
                  (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                    (∏ l, u l ^ decr β j l)))
              - ((Λ i c) * mainTerm u D w' β
                 + (c * (β i : R) * D i) * mainTerm u D w' (decr β i)
                 + ∑ j, (c * ((β j : R) *
                     (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                       mainTerm u D w' (decr β j))
            = (applyWord Λ w' ((Λ i c) * ∏ j, u j ^ β j) - (Λ i c) * mainTerm u D w' β)
              + (applyWord Λ w' ((c * (β i : R) * D i) * (∏ l, u l ^ decr β i l))
                 - (c * (β i : R) * D i) * mainTerm u D w' (decr β i))
              + (∑ j, (applyWord Λ w' ((c * ((β j : R) *
                    (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                      (∏ l, u l ^ decr β j l))
                  - (c * ((β j : R) *
                      (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                        mainTerm u D w' (decr β j))) := by
          rw [Finset.sum_sub_distrib]; ring
        rw [heq]
        exact Ideal.add_mem _ (Ideal.add_mem _ hA hB) (Ideal.sum_mem _ (fun j _ => hC j))
      have h2 : (Λ i c) * mainTerm u D w' β
            + (c * (β i : R) * D i) * mainTerm u D w' (decr β i)
            + (∑ j, (c * ((β j : R) *
                (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                  mainTerm u D w' (decr β j))
            - c * mainTerm u D (i :: w') β
          ∈ Jfilt 𝔎 u (Jidx β (w'.length + 1)) := by
        rw [mainterm_cons]
        have heq : (Λ i c) * mainTerm u D w' β
              + (c * (β i : R) * D i) * mainTerm u D w' (decr β i)
              + (∑ j, (c * ((β j : R) *
                  (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                    mainTerm u D w' (decr β j))
              - c * ((β i : R) * D i * mainTerm u D w' (decr β i))
            = (Λ i c) * mainTerm u D w' β
              + (∑ j, (c * ((β j : R) *
                  (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                    mainTerm u D w' (decr β j)) := by
          ring
        rw [heq]
        exact Ideal.add_mem _ hM1 (Ideal.sum_mem _ (fun j _ => hM3 j))
      have hfin : applyWord Λ w' ((Λ i c) * ∏ j, u j ^ β j)
            + applyWord Λ w' ((c * (β i : R) * D i) * (∏ l, u l ^ decr β i l))
            + (∑ j, applyWord Λ w' ((c * ((β j : R) *
                (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                  (∏ l, u l ^ decr β j l)))
            - c * mainTerm u D (i :: w') β
          = (applyWord Λ w' ((Λ i c) * ∏ j, u j ^ β j)
              + applyWord Λ w' ((c * (β i : R) * D i) * (∏ l, u l ^ decr β i l))
              + (∑ j, applyWord Λ w' ((c * ((β j : R) *
                  (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                    (∏ l, u l ^ decr β j l)))
              - ((Λ i c) * mainTerm u D w' β
                 + (c * (β i : R) * D i) * mainTerm u D w' (decr β i)
                 + ∑ j, (c * ((β j : R) *
                     (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                       mainTerm u D w' (decr β j)))
            + (((Λ i c) * mainTerm u D w' β
                 + (c * (β i : R) * D i) * mainTerm u D w' (decr β i)
                 + ∑ j, (c * ((β j : R) *
                     (Λ i (u j) - D j * (if i = j then (1 : R) else 0)))) *
                       mainTerm u D w' (decr β j))
               - c * mainTerm u D (i :: w') β) := by ring
      rw [hfin, ← hJt]
      exact Ideal.add_mem _ h1 h2

/-- Coefficient extraction (Philippon 4.6–4.7, the algebraic core). -/
theorem extract_coeff {R : Type*} [CommRing R] [Algebra ℂ R] {ℓ : ℕ}
    (𝔎 : Ideal R) (Λ : Fin ℓ → R → R) (u D : Fin ℓ → R)
    (hadd : ∀ i x y, Λ i (x + y) = Λ i x + Λ i y)
    (hleib : ∀ i x y, Λ i (x * y) = Λ i x * y + x * Λ i y)
    (hu : ∀ j, u j ∈ 𝔎)
    (hcong : ∀ i j, Λ i (u j) - D j * (if i = j then (1 : R) else 0) ∈ 𝔎)
    {τ : ℕ} (α : Fin ℓ → ℕ) (hα : ∑ i, α i = τ) (C : (Fin ℓ → ℕ) → R)
    (hX : applyL Λ α (weightedSum u τ C) ∈ 𝔎) :
    ((∏ i, (α i).factorial : ℕ) : R) * (∏ i, D i ^ (α i)) * C α ∈ 𝔎 := by
  classical
  set s : Finset (Fin ℓ → ℕ) :=
    (Fintype.piFinset (fun _ : Fin ℓ => Finset.range (τ + 1))).filter
      (fun β => ∑ i, β i = τ) with hs
  have hterm : ∀ β ∈ s, applyWord Λ (wordOf α) (C β * ∏ i, u i ^ β i)
      - C β * ((∏ i, ((β i).descFactorial (α i) : R)) * (∏ i, D i ^ (α i)) *
          (∏ i, u i ^ (β i - α i))) ∈ 𝔎 := by
    intro β hβ
    rw [hs, Finset.mem_filter] at hβ
    obtain ⟨_, hβsum⟩ := hβ
    have hinv := word_inv Λ u D 𝔎 hadd hleib hcong (wordOf α) (C β) β
    rw [mainTerm_wordOf] at hinv
    have hidx : Jidx β (wordOf α).length = 1 := by
      have hlen := (wordof_facts α).2
      simp only [Jidx, hlen, hβsum, hα]
      omega
    rw [hidx] at hinv
    exact (Jfilt_le_𝔎 hu le_rfl) hinv
  have hsum0 : (∑ β ∈ s, (applyWord Λ (wordOf α) (C β * ∏ i, u i ^ β i)
      - C β * ((∏ i, ((β i).descFactorial (α i) : R)) * (∏ i, D i ^ (α i)) *
          (∏ i, u i ^ (β i - α i))))) ∈ 𝔎 :=
    Ideal.sum_mem _ (fun β hβ => hterm β hβ)
  have hsum1 : (∑ β ∈ s, applyWord Λ (wordOf α) (C β * ∏ i, u i ^ β i))
      - (∑ β ∈ s, C β * ((∏ i, ((β i).descFactorial (α i) : R)) * (∏ i, D i ^ (α i)) *
          (∏ i, u i ^ (β i - α i)))) ∈ 𝔎 := by
    rw [← Finset.sum_sub_distrib]
    exact hsum0
  have hX' : (∑ β ∈ s, applyWord Λ (wordOf α) (C β * ∏ i, u i ^ β i)) ∈ 𝔎 := by
    rw [← applyWord_sum Λ hadd s (fun β => C β * ∏ i, u i ^ β i) (wordOf α)]
    have hws : (∑ β ∈ s, C β * ∏ i, u i ^ β i) = weightedSum u τ C := by
      rw [weightedSum, ← hs]
    rw [hws, ← applyl_eq]
    exact hX
  have hG : (∑ β ∈ s, C β * ((∏ i, ((β i).descFactorial (α i) : R)) * (∏ i, D i ^ (α i)) *
      (∏ i, u i ^ (β i - α i)))) ∈ 𝔎 := by
    have h := Ideal.sub_mem _ hX' hsum1
    convert h using 1
    ring
  have hαmem : α ∈ s := by
    rw [hs, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => Finset.mem_range.mpr ?_, hα⟩
    have h : α i ≤ τ := by
      simpa [hα] using Finset.single_le_sum (f := α) (fun j _ => Nat.zero_le (α j))
        (Finset.mem_univ i)
    omega
  have hcollapse : (∑ β ∈ s, C β * ((∏ i, ((β i).descFactorial (α i) : R)) *
      (∏ i, D i ^ (α i)) * (∏ i, u i ^ (β i - α i))))
      = C α * ((∏ i, ((α i).descFactorial (α i) : R)) * (∏ i, D i ^ (α i)) *
          (∏ i, u i ^ (α i - α i))) := by
    refine Finset.sum_eq_single α ?_ ?_
    · intro b hb hne
      rw [hs, Finset.mem_filter] at hb
      obtain ⟨_, hbsum⟩ := hb
      have hex : ∃ i, b i < α i := by
        by_contra hcon
        push_neg at hcon
        refine hne (funext fun i => ?_)
        have hsum : ∑ j, (b j - α j) = 0 := by
          have h1 : ∑ j, b j = ∑ j, α j + ∑ j, (b j - α j) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun j _ => (Nat.add_sub_of_le (hcon j)).symm)
          rw [hbsum, hα] at h1
          omega
        have hle := Finset.single_le_sum (f := fun j => b j - α j)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        have hz : b i - α i = 0 := by omega
        have hge : α i ≤ b i := hcon i
        omega
      obtain ⟨i0, hi0⟩ := hex
      have hzero : ((b i0).descFactorial (α i0) : R) = 0 := by
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hi0, Nat.cast_zero]
      have hprod : (∏ i, ((b i).descFactorial (α i) : R)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i0) hzero
      rw [hprod]
      ring
    · intro hnot
      exact absurd hαmem hnot
  have hval : C α * ((∏ i, ((α i).descFactorial (α i) : R)) * (∏ i, D i ^ (α i)) *
      (∏ i, u i ^ (α i - α i)))
      = ((∏ i, (α i).factorial : ℕ) : R) * (∏ i, D i ^ (α i)) * C α := by
    simp only [Nat.descFactorial_self, Nat.sub_self, pow_zero, Finset.prod_const_one, mul_one]
    rw [← Nat.cast_prod]
    ring
  rw [hcollapse] at hG
  rw [hval] at hG
  exact hG

end Work.BW
