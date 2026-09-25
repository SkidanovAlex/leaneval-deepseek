import Mathlib
import Submission.Work.NN.Final.one_sided_extension_le_of_discExt
import Submission.Work.NN.Final.discExtOfFlat
import Submission.Work.NN.Final.Defs

namespace Work.NN.PolarChain

open scoped NNReal ENNReal ContDiff
open Set Metric

open Work.NN.Final
open Work.CR.Flat

theorem one_sided_extension_finite {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 1 < c) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (v : (Fin n → ℂ) → ℂ),
      (∀ m : ℕ, m ≤ k → ContDiffOn ℝ (m : WithTop ENat) v (Work.NN.Final.pd n ρ 1)) →
      Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) ≠ ⊤ →
      ∃ w : (Fin n → ℂ) → ℂ,
        ContDiffOn ℝ (k : WithTop ENat) w (Work.NN.Final.pd n ρ c) ∧
        (∀ z ∈ Work.NN.Final.pd n ρ 1, w z = v z) ∧
        Work.CR.Flat.holderNorm k α w (Work.NN.Final.pd n ρ c)
          ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) := by
  have hD0 : Work.NN.Final.DiscExt.{0} α c :=
    Work.NN.Final.discExtOfFlat.{0} hα0 hα1 hc
  have hmu0_pd : polydisc 0 (interRadii ρ c 0) = Work.NN.Final.pd n ρ 1 := by
    have h1 : interRadii ρ c 0 = fun j => 1 * ρ j := by
      funext j
      rw [interRadii_apply, if_neg (Nat.not_lt_zero _), one_mul]
    rw [h1]; rfl
  have hmun_pd : polydisc 0 (interRadii ρ c n) = Work.NN.Final.pd n ρ c := by
    have h1 : interRadii ρ c n = fun j => c * ρ j := by
      funext j
      rw [interRadii_apply, if_pos j.isLt]
    rw [h1]; rfl
  have hmono : ∀ {i i' : ℕ}, i ≤ i' →
      polydisc 0 (interRadii ρ c i) ⊆ polydisc 0 (interRadii ρ c i') := by
    intro i i' hii'
    refine polydisc_mono fun j => ?_
    rw [interRadii_apply, interRadii_apply]
    by_cases h : (j : ℕ) < i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]
      by_cases h2 : (j : ℕ) < i'
      · rw [if_pos h2]
        exact le_mul_of_one_le_left (le_of_lt (hρ j)) (le_of_lt hc)
      · rw [if_neg h2]
  have hsucc : ∀ (i : ℕ) (hi : i < n),
      interRadii ρ c (i + 1) =
        Function.update (interRadii ρ c i) ⟨i, hi⟩ (c * interRadii ρ c i ⟨i, hi⟩) := by
    intro i hi
    funext j
    rw [interRadii_apply, Function.update_apply]
    by_cases h : j = ⟨i, hi⟩
    · subst h
      rw [if_pos (by simp), if_pos rfl]
      congr 1
      rw [interRadii_apply, Fin.val_mk, if_neg (lt_irrefl i)]
    · rw [if_neg h, interRadii_apply]
      have hj : (j : ℕ) ≠ i := fun hh => h (Fin.ext hh)
      by_cases h2 : (j : ℕ) < i
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  have hσi : ∀ i : Fin n, 0 < interRadii ρ c i i := by
    intro i
    rw [interRadii_apply, if_neg (lt_irrefl _)]
    exact hρ i
  have key : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (v : (Fin n → ℂ) → ℂ),
      (∀ m : ℕ, m ≤ k → ContDiffOn ℝ (m : WithTop ENat) v (Work.NN.Final.pd n ρ 1)) →
      Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) ≠ ⊤ →
      ∃ w : (Fin n → ℂ) → ℂ,
        ContDiffOn ℝ (k : WithTop ENat) w (Work.NN.Final.pd n ρ c) ∧
        (∀ z ∈ Work.NN.Final.pd n ρ 1, w z = v z) ∧
        Work.CR.Flat.holderNorm k α w (Work.NN.Final.pd n ρ c)
          ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) := by
    intro k
    choose E hEpos hEspec using fun i : Fin n =>
      exists_extension_coord (i := i) hα0 hD0 (σ := interRadii ρ c i) (hσi i)
    set D : ℝ := (∑ i : Fin n, E i k) + 1 with hDdef
    have hsum0 : 0 ≤ ∑ i : Fin n, E i k := Finset.sum_nonneg fun i _ => (hEpos i k).le
    have hDpos : 0 < D := by rw [hDdef]; linarith
    have hEle : ∀ i : Fin n, E i k ≤ D := by
      intro i
      have h1 : E i k ≤ ∑ j : Fin n, E j k :=
        Finset.single_le_sum (fun j _ => (hEpos j k).le) (Finset.mem_univ i)
      rw [hDdef]; linarith
    refine ⟨D ^ n, pow_pos hDpos n, fun v hv hvfin => ?_⟩
    have hv' : ∀ m : ℕ, m ≤ k →
        ContDiffOn ℝ (m : WithTop ENat) v (polydisc 0 (interRadii ρ c 0)) := by
      intro m hm
      rw [hmu0_pd]
      exact hv m hm
    have hvfin' : Work.CR.Flat.holderNorm k α v (polydisc 0 (interRadii ρ c 0)) ≠ ⊤ := by
      rw [hmu0_pd]; exact hvfin
    have aux : ∀ i ≤ n, ∃ (f : (Fin n → ℂ) → ℂ),
        ContDiffOn ℝ (k : WithTop ENat) f (polydisc 0 (interRadii ρ c i)) ∧
        (∀ z ∈ polydisc 0 (interRadii ρ c 0), f z = v z) ∧
        Work.CR.Flat.holderNorm k α f (polydisc 0 (interRadii ρ c i))
          ≤ ENNReal.ofReal (D ^ i) *
            Work.CR.Flat.holderNorm k α v (polydisc 0 (interRadii ρ c 0)) := by
      intro i
      induction i with
      | zero =>
          intro _
          exact ⟨v, hv' k le_rfl, fun z hz => rfl, by
            rw [pow_zero, ENNReal.ofReal_one, one_mul]⟩
      | succ i ih =>
          intro hk1
          have hi_lt : i < n := Nat.lt_of_succ_le hk1
          have hk : i ≤ n := Nat.le_of_lt hi_lt
          obtain ⟨f, hfsm, hfag, hfnorm⟩ := ih hk
          have hfne : Work.CR.Flat.holderNorm k α f (polydisc 0 (interRadii ρ c i)) ≠ ⊤ :=
            ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvfin') hfnorm
          obtain ⟨f', hf'sm, hf'ag, hf'norm⟩ :=
            hEspec ⟨i, hi_lt⟩ k f (fun m hm => hfsm.of_le (by exact_mod_cast hm)) hfne
          refine ⟨f', ?_, ?_, ?_⟩
          · rw [hsucc i hi_lt]; exact hf'sm
          · intro z hz
            rw [hf'ag z (hmono (Nat.zero_le i) hz), hfag z hz]
          · rw [hsucc i hi_lt]
            calc Work.CR.Flat.holderNorm k α f'
                  (polydisc 0 (Function.update (interRadii ρ c i) ⟨i, hi_lt⟩
                    (c * interRadii ρ c i ⟨i, hi_lt⟩)))
                ≤ ENNReal.ofReal (E ⟨i, hi_lt⟩ k) *
                    Work.CR.Flat.holderNorm k α f (polydisc 0 (interRadii ρ c i)) := hf'norm
              _ ≤ ENNReal.ofReal D * (ENNReal.ofReal (D ^ i) *
                    Work.CR.Flat.holderNorm k α v (polydisc 0 (interRadii ρ c 0))) :=
                  mul_le_mul' (ENNReal.ofReal_le_ofReal (hEle ⟨i, hi_lt⟩)) hfnorm
              _ = ENNReal.ofReal (D ^ (i + 1)) *
                    Work.CR.Flat.holderNorm k α v (polydisc 0 (interRadii ρ c 0)) := by
                  rw [pow_succ', ENNReal.ofReal_mul hDpos.le]
                  ring
    obtain ⟨f, hfsm, hfag, hfnorm⟩ := aux n le_rfl
    exact ⟨f, by rwa [hmun_pd] at hfsm,
      fun z hz => hfag z (by rwa [← hmu0_pd] at hz),
      by rwa [hmun_pd, hmu0_pd] at hfnorm⟩
  choose C hCpos hCspec using key
  exact ⟨C, hCpos, hCspec⟩

end Work.NN.PolarChain
