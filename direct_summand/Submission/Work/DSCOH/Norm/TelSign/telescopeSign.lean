/-
Area DSCOH (curric-46) — the sign identity of the "telescoping" of the leftover terms
of the first (sorting) homotopy of Stacks 20.23.6 (Tag 01FG).

The main content: for `x : Fin (k+2) → ι` and a slot `a : Fin (k+1)` one has
`signA x (a+1) = (-1)^(rankA x a) * signA x a` (here `signA x a` is the sign of the
permutation `sigmaA x a` agreeing with `Tuple.sort x` below `a` and increasing above `a`),
which is deduced from the *permutation* identity
`sigmaAPerm x a = sigmaAPerm x (a+1) * cycleIcc a (a + rankA x a)`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.ReadFib.readAFiber

open Work.DSCOH.Norm

namespace Work.DSCOH.Norm.TelSign

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.deprecated false

theorem headVal_succ_compl {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+1)) :
    (headVal x (Fin.succ a))ᶜ =
      ((headVal x (Fin.castSucc a))ᶜ).erase (Tuple.sort x (Fin.castSucc a)) := by
  have hins : headVal x (Fin.succ a)
      = insert (Tuple.sort x (Fin.castSucc a)) (headVal x (Fin.castSucc a)) := by
    have hfilter : (Finset.univ.filter (fun j : Fin (k+2) => (j:ℕ) < (Fin.succ a : ℕ)))
        = insert (Fin.castSucc a)
            (Finset.univ.filter (fun j : Fin (k+2) => (j:ℕ) < (Fin.castSucc a : ℕ))) := by
      ext jj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      rw [Fin.val_succ, Fin.val_castSucc]
      constructor
      · intro h
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h' | h'
        · exact Or.inr h'
        · exact Or.inl (Fin.ext (by rw [Fin.val_castSucc]; exact h'))
      · rintro (rfl | h)
        · rw [Fin.val_castSucc]; omega
        · omega
    rw [headVal, headVal, hfilter, Finset.image_insert]
  rw [hins, Finset.compl_insert]

theorem tailEmb_succ_lt {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+1))
    (i : Fin ((k+2) - (Fin.succ a).val)) (hi : (i:ℕ) < rankA x (Fin.castSucc a)) :
    tailEmb x (Fin.succ a) i =
      tailEmb x (Fin.castSucc a) ⟨(i:ℕ), by
        have h := rankA_lt x (Fin.castSucc a); rw [compl_card] at h; omega⟩ := by
  have hp : (i:ℕ) < (k+2) - (Fin.castSucc a).val := by
    have h := rankA_lt x (Fin.castSucc a); rw [compl_card] at h
    have hv : (Fin.castSucc a).val = a.val := Fin.val_castSucc a
    omega
  have hr : rankA x (Fin.castSucc a) < (k+2) - (Fin.castSucc a).val := by
    have h := rankA_lt x (Fin.castSucc a); rw [compl_card] at h
    have hv : (Fin.castSucc a).val = a.val := Fin.val_castSucc a
    omega
  have hlt : tailEmb x (Fin.castSucc a) ⟨(i:ℕ), hp⟩ < Tuple.sort x (Fin.castSucc a) := by
    have hs := (tailEmb x (Fin.castSucc a)).strictMono
      (show (⟨(i:ℕ), hp⟩ : Fin ((k+2) - (Fin.castSucc a).val))
          < ⟨rankA x (Fin.castSucc a), hr⟩ from Fin.lt_def.mpr hi)
    rwa [ReadFib.tailEmb_rankA x (Fin.castSucc a)] at hs
  rw [ReadFib.tailEmb_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [headVal_succ_compl x a, Finset.mem_erase]
    refine ⟨?_, Finset.mem_compl.mpr (tailEmb_mem x (Fin.castSucc a) _)⟩
    intro hcon
    have h1 : tailEmb x (Fin.castSucc a) ⟨(i:ℕ), hp⟩
        = tailEmb x (Fin.castSucc a) ⟨rankA x (Fin.castSucc a), hr⟩ :=
      hcon.trans (ReadFib.tailEmb_rankA x (Fin.castSucc a)).symm
    have h2 := congrArg Fin.val ((tailEmb x (Fin.castSucc a)).injective h1)
    omega
  · have hc : (i:ℕ) = (((headVal x (Fin.castSucc a))ᶜ).filter
        (fun v => v < tailEmb x (Fin.castSucc a) ⟨(i:ℕ), hp⟩)).card :=
      ((ReadFib.tailEmb_eq_iff x (Fin.castSucc a) ⟨(i:ℕ), hp⟩
        (tailEmb x (Fin.castSucc a) ⟨(i:ℕ), hp⟩)).mp rfl).2
    rw [headVal_succ_compl x a, Finset.filter_erase,
      Finset.erase_eq_self.mpr (by
        simp only [Finset.mem_filter]
        rintro ⟨-, hlt2⟩
        exact absurd hlt2 (not_lt.mpr hlt.le))]
    exact hc

theorem tailEmb_succ_ge {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+1))
    (i : Fin ((k+2) - (Fin.succ a).val)) (hi : rankA x (Fin.castSucc a) ≤ (i:ℕ)) :
    tailEmb x (Fin.succ a) i =
      tailEmb x (Fin.castSucc a) ⟨(i:ℕ)+1, by
        have h := i.isLt
        have hc : (Fin.castSucc a).val = a.val := Fin.val_castSucc a
        have hs : (Fin.succ a).val = a.val + 1 := Fin.val_succ a
        omega⟩ := by
  have hp : (i:ℕ)+1 < (k+2) - (Fin.castSucc a).val := by
    have h := i.isLt
    have hc : (Fin.castSucc a).val = a.val := Fin.val_castSucc a
    have hs : (Fin.succ a).val = a.val + 1 := Fin.val_succ a
    omega
  have hr : rankA x (Fin.castSucc a) < (k+2) - (Fin.castSucc a).val := by
    have h := rankA_lt x (Fin.castSucc a); rw [compl_card] at h
    have hv : (Fin.castSucc a).val = a.val := Fin.val_castSucc a
    omega
  have hgt : Tuple.sort x (Fin.castSucc a) < tailEmb x (Fin.castSucc a) ⟨(i:ℕ)+1, hp⟩ := by
    have hs := (tailEmb x (Fin.castSucc a)).strictMono
      (show (⟨rankA x (Fin.castSucc a), hr⟩ : Fin ((k+2) - (Fin.castSucc a).val))
          < ⟨(i:ℕ)+1, hp⟩ from Fin.lt_def.mpr (by simpa using Nat.lt_succ_of_le hi))
    rwa [ReadFib.tailEmb_rankA x (Fin.castSucc a)] at hs
  rw [ReadFib.tailEmb_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [headVal_succ_compl x a, Finset.mem_erase]
    refine ⟨?_, Finset.mem_compl.mpr (tailEmb_mem x (Fin.castSucc a) _)⟩
    intro hcon
    have h1 : tailEmb x (Fin.castSucc a) ⟨(i:ℕ)+1, hp⟩
        = tailEmb x (Fin.castSucc a) ⟨rankA x (Fin.castSucc a), hr⟩ :=
      hcon.trans (ReadFib.tailEmb_rankA x (Fin.castSucc a)).symm
    have h2 := congrArg Fin.val ((tailEmb x (Fin.castSucc a)).injective h1)
    omega
  · have hc : (i:ℕ)+1 = (((headVal x (Fin.castSucc a))ᶜ).filter
        (fun v => v < tailEmb x (Fin.castSucc a) ⟨(i:ℕ)+1, hp⟩)).card :=
      ((ReadFib.tailEmb_eq_iff x (Fin.castSucc a) ⟨(i:ℕ)+1, hp⟩
        (tailEmb x (Fin.castSucc a) ⟨(i:ℕ)+1, hp⟩)).mp rfl).2
    rw [headVal_succ_compl x a, Finset.filter_erase,
      Finset.card_erase_of_mem (Finset.mem_filter.mpr
        ⟨sortA_mem_compl x (Fin.castSucc a), hgt⟩)]
    omega

/-- The position at which the "second read" of `Tuple.sort x (castSucc a)` takes place. -/
noncomputable def mrA {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+1)) : Fin (k+2) :=
  ⟨(a:ℕ) + rankA x (Fin.castSucc a), by
    have h := rankA_lt x (Fin.castSucc a)
    rw [compl_card] at h
    have hv : ((Fin.castSucc a : Fin (k+2)) : ℕ) = (a:ℕ) := Fin.val_castSucc a
    have ha : (a:ℕ) < k+1 := a.isLt
    omega⟩

lemma mrA_val {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+1)) :
    ((mrA x a : Fin (k+2)) : ℕ) = (a:ℕ) + rankA x (Fin.castSucc a) := rfl

lemma rankA_lt_sub {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+2)) :
    rankA x a < (k+2) - (a:ℕ) := by
  have h := rankA_lt x a
  rw [compl_card] at h
  exact h

lemma mrA_le {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+1)) :
    (Fin.castSucc a) ≤ mrA x a :=
  Fin.le_def.mpr (Nat.le_add_right _ _)

lemma fin_succ_val {n : ℕ} [NeZero n] (k : Fin n) (h : (k:ℕ)+1 < n) :
    ((k + 1 : Fin n) : ℕ) = (k:ℕ)+1 := by
  have hn : 1 < n := by omega
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hn]
  exact Nat.mod_eq_of_lt h

theorem sigmaAPerm_succ_cycle {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+1)) :
    sigmaAPerm x (Fin.castSucc a)
      = sigmaAPerm x (Fin.succ a) * Fin.cycleIcc (Fin.castSucc a) (mrA x a) := by
  haveI : NeZero (k+2) := ⟨by omega⟩
  have hc : ((Fin.castSucc a : Fin (k+2)) : ℕ) = (a:ℕ) := Fin.val_castSucc a
  have hs : ((Fin.succ a : Fin (k+2)) : ℕ) = (a:ℕ) + 1 := Fin.val_succ a
  have hmrv : ((mrA x a : Fin (k+2)) : ℕ) = (a:ℕ) + rankA x (Fin.castSucc a) := rfl
  have hmrlt : ((mrA x a : Fin (k+2)) : ℕ) < k+2 := (mrA x a).isLt
  apply Equiv.ext
  intro j
  simp only [Equiv.Perm.mul_apply, sigmaAPerm_apply]
  rcases lt_trichotomy (j:ℕ) (a:ℕ) with hlt | heq | hgt
  · have hcj : (Fin.cycleIcc (Fin.castSucc a) (mrA x a)) j = j :=
      Fin.cycleIcc_of_lt (Fin.lt_def.mpr hlt)
    rw [hcj, sigmaA_head x (Fin.castSucc a) hlt,
      sigmaA_head x (Fin.succ a) (by rw [hs]; omega)]
  · have hj : j = Fin.castSucc a := Fin.ext heq
    rw [hj]
    by_cases hm : (Fin.castSucc a) = mrA x a
    · have hcm : (Fin.cycleIcc (Fin.castSucc a) (mrA x a)) (Fin.castSucc a) = Fin.castSucc a := by
        rw [Fin.cycleIcc_of_le_of_le (i := Fin.castSucc a) (j := mrA x a)
          (k := Fin.castSucc a) (le_refl _) (mrA_le x a), if_pos hm]
      have hr0 : rankA x (Fin.castSucc a) = 0 := by
        have hv := congrArg (fun t : Fin (k+2) => ((t:Fin (k+2)):ℕ)) hm
        rw [hmrv, hc] at hv
        omega
      have hval : ((Fin.castSucc a : Fin (k+2)) : ℕ) - ((Fin.castSucc a : Fin (k+2)) : ℕ)
          = rankA x (Fin.castSucc a) := by
        rw [Nat.sub_self, hr0]
      rw [hcm, sigmaA_head x (Fin.succ a) (by rw [hc, hs]; omega),
        sigmaA_tail x (Fin.castSucc a) (by rw [hc]; exact lt_irrefl _)]
      rw [show (⟨↑(Fin.castSucc a) - ↑(Fin.castSucc a),
            by omega⟩ : Fin ((k+2) - ↑(Fin.castSucc a)))
          = ⟨rankA x (Fin.castSucc a), rankA_lt_sub x (Fin.castSucc a)⟩ from Fin.ext hval]
      exact ReadFib.tailEmb_rankA x (Fin.castSucc a)
    · have hcm : (Fin.cycleIcc (Fin.castSucc a) (mrA x a)) (Fin.castSucc a) = Fin.succ a := by
        rw [Fin.cycleIcc_of_le_of_le (i := Fin.castSucc a) (j := mrA x a)
          (k := Fin.castSucc a) (le_refl _) (mrA_le x a), if_neg hm]
        exact Fin.ext (by rw [fin_succ_val (Fin.castSucc a) (by omega), hs, hc])
      have hrpos : 0 < rankA x (Fin.castSucc a) := by
        rcases Nat.eq_zero_or_pos (rankA x (Fin.castSucc a)) with h0 | hpos
        · exact absurd (Fin.ext (by rw [hmrv, hc, h0]; omega)) hm
        · exact hpos
      have hval1 : ((Fin.castSucc a : Fin (k+2)) : ℕ) - ((Fin.castSucc a : Fin (k+2)) : ℕ) = 0 :=
        Nat.sub_self _
      have hval2 : ((Fin.succ a : Fin (k+2)) : ℕ) - ((Fin.succ a : Fin (k+2)) : ℕ) = 0 :=
        Nat.sub_self _
      rw [hcm, sigmaA_tail x (Fin.castSucc a) (by rw [hc]; exact lt_irrefl _),
        sigmaA_tail x (Fin.succ a) (by rw [hs]; exact lt_irrefl _)]
      rw [show (⟨↑(Fin.castSucc a) - ↑(Fin.castSucc a),
            by omega⟩ : Fin ((k+2) - ↑(Fin.castSucc a)))
          = ⟨(0:ℕ), by omega⟩ from Fin.ext hval1,
        show (⟨↑(Fin.succ a) - ↑(Fin.succ a),
            by omega⟩ : Fin ((k+2) - ↑(Fin.succ a)))
          = ⟨(0:ℕ), by omega⟩ from Fin.ext hval2]
      exact (tailEmb_succ_lt x a ⟨0, by rw [hs]; omega⟩ hrpos).symm
  · rcases lt_trichotomy (j:ℕ) ((mrA x a : Fin (k+2)) : ℕ) with h3a | h3b | h3c
    · have hcj : (Fin.cycleIcc (Fin.castSucc a) (mrA x a)) j = ⟨(j:ℕ)+1, by omega⟩ := by
        rw [Fin.cycleIcc_of_le_of_le (i := Fin.castSucc a) (j := mrA x a) (k := j)
          (by rw [Fin.le_def]; omega) (by rw [Fin.le_def]; omega),
          if_neg (by intro hcon; rw [hcon] at h3a; exact lt_irrefl _ h3a)]
        exact Fin.ext (fin_succ_val j (by omega))
      have hu : (j:ℕ) - (a:ℕ) < rankA x (Fin.castSucc a) := by omega
      have hb : (j:ℕ) - (a:ℕ) < (k+2) - ((Fin.succ a : Fin (k+2)) : ℕ) := by omega
      have hb' : (j:ℕ) - (a:ℕ) < (k+2) - ((Fin.castSucc a : Fin (k+2)) : ℕ) := by omega
      have hval1 : ((j:ℕ) - ((Fin.castSucc a : Fin (k+2)) : ℕ)) = (j:ℕ) - (a:ℕ) := by rw [hc]
      have hval2 : (((⟨(j:ℕ)+1, by omega⟩ : Fin (k+2)) : ℕ) - ((Fin.succ a : Fin (k+2)) : ℕ))
          = (j:ℕ) - (a:ℕ) := by
        show ((j:ℕ) + 1) - ((a:ℕ) + 1) = (j:ℕ) - (a:ℕ)
        omega
      rw [hcj, sigmaA_tail x (Fin.castSucc a) (by omega),
        sigmaA_tail x (Fin.succ a) (by omega)]
      rw [show (⟨↑j - ↑(Fin.castSucc a),
            by omega⟩ : Fin ((k+2) - ↑(Fin.castSucc a)))
          = ⟨(j:ℕ) - (a:ℕ), hb'⟩ from Fin.ext hval1,
        show (⟨↑(⟨(j:ℕ)+1, by omega⟩ : Fin (k+2)) - ↑(Fin.succ a),
            by omega⟩ : Fin ((k+2) - ↑(Fin.succ a)))
          = ⟨(j:ℕ) - (a:ℕ), hb⟩ from Fin.ext hval2]
      exact (tailEmb_succ_lt x a ⟨(j:ℕ) - (a:ℕ), hb⟩ hu).symm
    · have hj : j = mrA x a := Fin.ext h3b
      rw [hj]
      have hval : ((mrA x a : Fin (k+2)) : ℕ) - ((Fin.castSucc a : Fin (k+2)) : ℕ)
          = rankA x (Fin.castSucc a) := by
        rw [hmrv, hc]
        omega
      rw [Fin.cycleIcc_of_last (i := Fin.castSucc a) (j := mrA x a) (mrA_le x a),
        sigmaA_head x (Fin.succ a) (by rw [hc, hs]; omega),
        sigmaA_tail x (Fin.castSucc a) (by omega)]
      rw [show (⟨↑(mrA x a) - ↑(Fin.castSucc a),
            by omega⟩ : Fin ((k+2) - ↑(Fin.castSucc a)))
          = ⟨rankA x (Fin.castSucc a), rankA_lt_sub x (Fin.castSucc a)⟩ from Fin.ext hval]
      exact ReadFib.tailEmb_rankA x (Fin.castSucc a)
    · have hcj : (Fin.cycleIcc (Fin.castSucc a) (mrA x a)) j = j :=
        Fin.cycleIcc_of_gt (Fin.lt_def.mpr h3c)
      have hle : rankA x (Fin.castSucc a) ≤ (j:ℕ) - ((Fin.succ a : Fin (k+2)) : ℕ) := by omega
      have hb : (j:ℕ) - ((Fin.succ a : Fin (k+2)) : ℕ) <
          (k+2) - ((Fin.succ a : Fin (k+2)) : ℕ) := by omega
      have hb' : (j:ℕ) - ((Fin.castSucc a : Fin (k+2)) : ℕ) <
          (k+2) - ((Fin.castSucc a : Fin (k+2)) : ℕ) := by omega
      have hval : ((j:ℕ) - ((Fin.succ a : Fin (k+2)) : ℕ)) + 1
          = (j:ℕ) - ((Fin.castSucc a : Fin (k+2)) : ℕ) := by
        rw [hs, hc]
        omega
      rw [hcj, sigmaA_tail x (Fin.castSucc a) (by omega),
        sigmaA_tail x (Fin.succ a) (by omega)]
      rw [tailEmb_succ_ge x a ⟨(j:ℕ) - ↑(Fin.succ a), hb⟩ hle,
        show (⟨(j:ℕ) - ↑(Fin.succ a) + 1,
            by omega⟩ : Fin ((k+2) - ↑(Fin.castSucc a)))
          = ⟨↑j - ↑(Fin.castSucc a), hb'⟩ from Fin.ext hval]


theorem signA_succ {k : ℕ} (x : Fin (k+2) → ι) (a : Fin (k+1)) :
    signA x (Fin.succ a) = (-1 : ℤ) ^ (rankA x (Fin.castSucc a)) * signA x (Fin.castSucc a) := by
  have hsign : Equiv.Perm.sign (sigmaAPerm x (Fin.castSucc a))
      = Equiv.Perm.sign (sigmaAPerm x (Fin.succ a)) * (-1 : ℤˣ) ^ rankA x (Fin.castSucc a) := by
    rw [sigmaAPerm_succ_cycle x a, Equiv.Perm.sign_mul]
    congr 1
    rw [Fin.sign_cycleIcc_of_le (mrA_le x a), mrA_val, Fin.val_castSucc]
    congr 1
    omega
  have h1 := congrArg (fun u : ℤˣ => (u : ℤ)) hsign
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h1
  have hval : (↑(-1 : ℤˣ) : ℤ) = -1 := by
    rw [Units.val_neg, Units.val_one]
  rw [hval] at h1
  have hsq : ((-1 : ℤ) ^ rankA x (Fin.castSucc a)) * ((-1 : ℤ) ^ rankA x (Fin.castSucc a)) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨rankA x (Fin.castSucc a), rfl⟩
  have h3 : signA x (Fin.castSucc a) * ((-1 : ℤ) ^ rankA x (Fin.castSucc a))
      = signA x (Fin.succ a) := by
    unfold signA
    rw [h1, mul_assoc, hsq, mul_one]
  rw [← h3]
  ring

/-- **The sign identity of the "telescoping" of the leftover terms** of the first (sorting)
homotopy of Stacks 20.23.6.  For `x : Fin (k+2) → ι` and a slot `a : Fin (k+1)`, the
`(a, pos2A x a)`-coefficient of the "read then delete" term (`(-1)^(a + pos2A x a)` times the
sign of `sigmaA x a`) is the negative of the `(a+1, a+1)`-coefficient, which is `signA x (a+1)`
because `(a+1) + (a+1)` is even. -/
theorem telescopeSign {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ} (x : Fin (k+2) → ι)
    (a : Fin (k+1)) :
    (-1 : ℤ) ^ ((Fin.castSucc a).val + (Work.DSCOH.Norm.pos2A x (Fin.castSucc a)).val) *
        Work.DSCOH.Norm.signA x (Fin.castSucc a) =
      - Work.DSCOH.Norm.signA x (Fin.succ a) := by
  rw [signA_succ x a]
  have hp : (pos2A x (Fin.castSucc a)).val = (a:ℕ) + 1 + rankA x (Fin.castSucc a) := rfl
  have hcc : (Fin.castSucc a).val = (a:ℕ) := rfl
  rw [hp, hcc]
  have hE : (-1 : ℤ) ^ ((a:ℕ) + ((a:ℕ) + 1 + rankA x (Fin.castSucc a)))
      = - ((-1 : ℤ) ^ rankA x (Fin.castSucc a)) := by
    have he : (a:ℕ) + ((a:ℕ) + 1 + rankA x (Fin.castSucc a))
        = rankA x (Fin.castSucc a) + (2 * (a:ℕ) + 1) := by ring
    rw [he, pow_add]
    have hodd : Odd (2 * (a:ℕ) + 1) := ⟨(a:ℕ), by ring⟩
    rw [hodd.neg_one_pow]
    ring
  rw [hE]
  ring

end Work.DSCOH.Norm.TelSign
