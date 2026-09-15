import Mathlib
import Submission.Commons.Combinatorics.Additive.Szemeredi.finite_of_prime_engine

open Finset

namespace Commons.Combinatorics.Additive.Szemeredi

private lemma sum_indicator_add_eq_card {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (c : ZMod p) :
    ∑ a : ZMod p, (if a + c ∈ A then (1:ℝ) else 0) = (A.card : ℝ) := by
  rw [Finset.sum_boole]
  have h : (Finset.univ.filter (fun a : ZMod p => a + c ∈ A)) = A.image (fun x => x - c) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx; exact ⟨x + c, hx, by ring⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [h]
  congr 1
  exact Finset.card_image_of_injOn (fun x _ y _ hxy => sub_left_inj.mp hxy)

private lemma window_sum_eq {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (M : ℕ) :
    ∑ a : ZMod p, ∑ d ∈ (Finset.univ : Finset (ZMod p)).erase (0 : ZMod p),
        (((Finset.range M).filter (fun i : ℕ => a + (i : ZMod p) * d ∈ A)).card : ℝ)
      = (A.card : ℝ) * (M : ℝ) * (((Finset.univ : Finset (ZMod p)).erase 0).card : ℝ) := by
  set D : Finset (ZMod p) := (Finset.univ : Finset (ZMod p)).erase 0 with hD
  set I : Finset ℕ := Finset.range M with hI
  set F : ZMod p → ZMod p → ℕ → ℝ :=
    fun a d i => (if a + (i : ZMod p) * d ∈ A then (1:ℝ) else 0) with hF
  have hg : ∀ a d, (((Finset.range M).filter (fun i : ℕ => a + (i : ZMod p) * d ∈ A)).card : ℝ)
      = ∑ i ∈ I, F a d i := by
    intro a d
    rw [hI, hF]
    exact (Finset.sum_boole (fun i : ℕ => a + (i : ZMod p) * d ∈ A) (Finset.range M)).symm
  have step1 : (∑ a : ZMod p, ∑ d ∈ D, ∑ i ∈ I, F a d i)
      = ∑ d ∈ D, ∑ a : ZMod p, ∑ i ∈ I, F a d i := Finset.sum_comm
  have step2 : (∑ d ∈ D, ∑ a : ZMod p, ∑ i ∈ I, F a d i)
      = ∑ d ∈ D, ∑ i ∈ I, ∑ a : ZMod p, F a d i := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    exact Finset.sum_comm
  have step3 : (∑ d ∈ D, ∑ i ∈ I, ∑ a : ZMod p, F a d i)
      = ∑ i ∈ I, ∑ d ∈ D, ∑ a : ZMod p, F a d i := Finset.sum_comm
  have step4 : ∀ i ∈ I, (∑ d ∈ D, ∑ a : ZMod p, F a d i) = (D.card : ℝ) * (A.card : ℝ) := by
    intro i _
    rw [Finset.sum_congr rfl (fun d _ => ?_)]
    · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    · rw [hF]
      exact sum_indicator_add_eq_card A ((i : ZMod p) * d)
  calc ∑ a : ZMod p, ∑ d ∈ D, (((Finset.range M).filter (fun i : ℕ => a + (i : ZMod p) * d ∈ A)).card : ℝ)
      = ∑ a : ZMod p, ∑ d ∈ D, ∑ i ∈ I, F a d i := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun d _ => hg a d))
    _ = ∑ d ∈ D, ∑ a : ZMod p, ∑ i ∈ I, F a d i := step1
    _ = ∑ d ∈ D, ∑ i ∈ I, ∑ a : ZMod p, F a d i := step2
    _ = ∑ i ∈ I, ∑ d ∈ D, ∑ a : ZMod p, F a d i := step3
    _ = ∑ i ∈ I, (D.card : ℝ) * (A.card : ℝ) := Finset.sum_congr rfl step4
    _ = (M : ℝ) * ((D.card : ℝ) * (A.card : ℝ)) := by
          rw [Finset.sum_const, hI, Finset.card_range, nsmul_eq_mul]
    _ = (A.card : ℝ) * (M : ℝ) * (D.card : ℝ) := by ring

private lemma card_erase_zero {p : ℕ} [NeZero p] :
    ((Finset.univ : Finset (ZMod p)).erase (0 : ZMod p)).card = p - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

private lemma natCast_ne_zero_of_lt {p s : ℕ} [NeZero p] (hs1 : 1 ≤ s) (hsp : s < p) :
    ((s : ℕ) : ZMod p) ≠ 0 := by
  intro h
  have hv : (((s : ℕ) : ZMod p)).val = 0 := (ZMod.val_eq_zero _).mpr h
  rw [ZMod.val_cast_of_lt hsp] at hv
  omega

private theorem varnavides_count
    (k : ℕ) (hk : 2 ≤ k) (M : ℕ) (hM : 1 ≤ M) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hint : ∀ S : Finset ℕ, S ⊆ Finset.range M → (θ/2) * (M : ℝ) ≤ (S.card : ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ S) :
    ∀ (p : ℕ) [NeZero p], Nat.Prime p → M ≤ p →
      ∀ A : Finset (ZMod p), θ * (p : ℝ) ≤ (A.card : ℝ) →
        (θ / (4 * (M : ℝ)^2)) * (p : ℝ)^2 ≤
          (((Finset.univ : Finset (ZMod p × ZMod p)).filter
            (fun q => q.2 ≠ 0 ∧ ∀ j : ℕ, j < k → q.1 + (j : ZMod p) * q.2 ∈ A)).card : ℝ) := by
  intro p _ hp hMp A hA
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Finset (ZMod p) := (Finset.univ : Finset (ZMod p)).erase 0 with hD
  set posOf : ZMod p × ZMod p → Finset ℕ :=
    fun w => (Finset.range M).filter (fun i : ℕ => w.1 + (i : ZMod p) * w.2 ∈ A) with hpos
  set f : ZMod p × ZMod p → ℝ := fun w => ((posOf w).card : ℝ) with hf
  set W : Finset (ZMod p × ZMod p) := (Finset.univ : Finset (ZMod p)) ×ˢ D with hW
  set Good : Finset (ZMod p × ZMod p) := W.filter (fun w => (θ/2) * (M:ℝ) ≤ f w) with hGood
  set APs : Finset (ZMod p × ZMod p) := (Finset.univ : Finset (ZMod p × ZMod p)).filter
    (fun q => q.2 ≠ 0 ∧ ∀ j : ℕ, j < k → q.1 + (j : ZMod p) * q.2 ∈ A) with hAPs
  have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hMpos : (0:ℝ) < (M:ℝ) := lt_of_lt_of_le one_pos hMR
  have hDcard : (D.card : ℝ) = (p:ℝ) - 1 := by
    rw [hD, card_erase_zero]
    have h1 : 1 ≤ p := hp.one_le
    push_cast [Nat.cast_sub h1]; ring
  have hWcard : (W.card : ℝ) = (p:ℝ) * ((p:ℝ) - 1) := by
    rw [hW, Finset.card_product, Finset.card_univ, ZMod.card]
    push_cast
    rw [hDcard]
  have hsum : ∑ w ∈ W, f w = (A.card : ℝ) * (M:ℝ) * (D.card : ℝ) := by
    rw [hW]
    rw [Finset.sum_product]
    have : ∀ a d, f (a,d) = (((Finset.range M).filter (fun i : ℕ => a + (i : ZMod p) * d ∈ A)).card : ℝ) := by
      intro a d; simp only [hf, hpos]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun d _ => this a d))]
    exact window_sum_eq A M
  have hGood_sub : Good ⊆ W := by rw [hGood]; exact Finset.filter_subset _ _
  have hbnd1 : ∑ w ∈ Good, f w ≤ (Good.card : ℝ) * (M:ℝ) := by
    have h1 : ∀ w ∈ Good, f w ≤ (M:ℝ) := by
      intro w _
      simp only [hf]
      have hc : (posOf w).card ≤ M := by
        calc (posOf w).card ≤ (Finset.range M).card := by
              apply Finset.card_le_card
              rw [hpos]; exact Finset.filter_subset _ _
          _ = M := Finset.card_range M
      exact_mod_cast hc
    calc ∑ w ∈ Good, f w ≤ ∑ _w ∈ Good, (M:ℝ) := Finset.sum_le_sum h1
      _ = (Good.card : ℝ) * (M:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hbnd2 : ∑ w ∈ W \ Good, f w ≤ ((W \ Good).card : ℝ) * ((θ/2) * (M:ℝ)) := by
    have h1 : ∀ w ∈ W \ Good, f w ≤ (θ/2) * (M:ℝ) := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      have hc : ¬ ((θ/2) * (M:ℝ) ≤ f w) := by
        intro hc; exact hw.2 (by rw [hGood]; exact Finset.mem_filter.mpr ⟨hw.1, hc⟩)
      exact le_of_lt (not_le.mp hc)
    calc ∑ w ∈ W \ Good, f w ≤ ∑ _w ∈ W \ Good, ((θ/2) * (M:ℝ)) := Finset.sum_le_sum h1
      _ = ((W \ Good).card : ℝ) * ((θ/2) * (M:ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hbnd : ∑ w ∈ W, f w ≤ (Good.card : ℝ) * (M:ℝ) + ((W \ Good).card : ℝ) * ((θ/2) * (M:ℝ)) := by
    rw [← Finset.sum_sdiff hGood_sub]
    exact le_trans (add_le_add hbnd2 hbnd1) (le_of_eq (add_comm _ _))
  have hkey : θ * (p:ℝ) * (M:ℝ) * (D.card:ℝ) ≤
      (Good.card:ℝ) * (M:ℝ) + ((W \ Good).card : ℝ) * ((θ/2) * (M:ℝ)) := by
    calc θ * (p:ℝ) * (M:ℝ) * (D.card:ℝ)
        = θ * (p:ℝ) * ((M:ℝ) * (D.card:ℝ)) := by ring
      _ ≤ (A.card:ℝ) * ((M:ℝ) * (D.card:ℝ)) := by
            apply mul_le_mul_of_nonneg_right hA; positivity
      _ = ∑ w ∈ W, f w := by rw [hsum]; ring
      _ ≤ _ := hbnd
  have hcmin : ((W \ Good).card : ℝ) = (W.card : ℝ) - (Good.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hGood_sub]
    exact Nat.cast_sub (Finset.card_le_card hGood_sub)
  have hGood_lb : (θ/2) * (p:ℝ) * ((p:ℝ) - 1) ≤ (Good.card : ℝ) := by
    have hkey2 : (M:ℝ) * (θ * (p:ℝ) * ((p:ℝ)-1)) ≤
        (M:ℝ) * ((Good.card:ℝ) + ((W \ Good).card : ℝ) * (θ/2)) := by
      have h1 : (M:ℝ) * (θ * (p:ℝ) * ((p:ℝ)-1)) = θ * (p:ℝ) * (M:ℝ) * (D.card:ℝ) := by
        rw [hDcard]; ring
      rw [h1]
      calc θ * (p:ℝ) * (M:ℝ) * (D.card:ℝ)
          ≤ (Good.card:ℝ) * (M:ℝ) + ((W \ Good).card : ℝ) * ((θ/2) * (M:ℝ)) := hkey
        _ = (M:ℝ) * ((Good.card:ℝ) + ((W \ Good).card : ℝ) * (θ/2)) := by ring
    have hkey3 : θ * (p:ℝ) * ((p:ℝ)-1) ≤ (Good.card:ℝ) + ((W \ Good).card : ℝ) * (θ/2) :=
      (mul_le_mul_iff_right₀ hMpos).mp hkey2
    have hGd0 : (0:ℝ) ≤ (Good.card:ℝ) := by positivity
    nlinarith [hkey3, hcmin, hWcard, hGd0, hθ1]
  -- choice of a sub-progression in each good window
  have hselect : ∀ w : ZMod p × ZMod p, w ∈ Good → ∃ pr : ℕ × ℕ,
      1 ≤ pr.2 ∧ pr.1 < M ∧ pr.2 < M ∧ ∀ j : ℕ, j < k → pr.1 + pr.2 * j ∈ posOf w := by
    intro w hw
    rw [hGood, Finset.mem_filter] at hw
    obtain ⟨hwW, hwgood⟩ := hw
    have hpos_sub : posOf w ⊆ Finset.range M := by rw [hpos]; exact Finset.filter_subset _ _
    have hcard : (θ/2) * (M:ℝ) ≤ ((posOf w).card : ℝ) := by simpa only [hf] using hwgood
    obtain ⟨a₀, b₀, hb₀, hmem⟩ := hint (posOf w) hpos_sub hcard
    have haM : a₀ < M := by
      have h0 := hmem 0 (by omega)
      rw [Nat.mul_zero, add_zero] at h0
      exact Finset.mem_range.mp (hpos_sub h0)
    have hbM : b₀ < M := by
      have hk1 : k - 1 < k := by omega
      have h0 := hmem (k-1) hk1
      have hlt : a₀ + b₀ * (k-1) < M := Finset.mem_range.mp (hpos_sub h0)
      have h1 : b₀ ≤ b₀ * (k-1) := by
        have h2 : 1 ≤ k - 1 := by omega
        simpa using Nat.mul_le_mul_left b₀ h2
      omega
    exact ⟨(a₀, b₀), hb₀, haM, hbM, hmem⟩
  let pr : {w : ZMod p × ZMod p // w ∈ Good} → ℕ × ℕ :=
    fun w => Classical.choose (hselect w.1 w.2)
  have hpr : ∀ w : {w : ZMod p × ZMod p // w ∈ Good},
      1 ≤ (pr w).2 ∧ (pr w).1 < M ∧ (pr w).2 < M ∧
        ∀ j : ℕ, j < k → (pr w).1 + (pr w).2 * j ∈ posOf w.1 :=
    fun w => Classical.choose_spec (hselect w.1 w.2)
  let wit : {w : ZMod p × ZMod p // w ∈ Good} → (ZMod p × ZMod p) × (Fin M × Fin M) :=
    fun w => ((w.1.1 + ((pr w).1 : ZMod p) * w.1.2, ((pr w).2 : ZMod p) * w.1.2),
              (⟨(pr w).1, (hpr w).2.1⟩, ⟨(pr w).2, (hpr w).2.2.1⟩))
  have hnonzero : ∀ w : {w : ZMod p × ZMod p // w ∈ Good}, ((pr w).2 : ZMod p) ≠ 0 :=
    fun w => natCast_ne_zero_of_lt (hpr w).1 (lt_of_lt_of_le (hpr w).2.2.1 hMp)
  have hwit_inj : Function.Injective wit := by
    intro w w' hww'
    have hq1 : w.1.1 + ((pr w).1 : ZMod p) * w.1.2 = w'.1.1 + ((pr w').1 : ZMod p) * w'.1.2 := by
      have := congrArg Prod.fst (congrArg Prod.fst hww')
      simpa only [wit] using this
    have hq2 : ((pr w).2 : ZMod p) * w.1.2 = ((pr w').2 : ZMod p) * w'.1.2 := by
      have := congrArg Prod.snd (congrArg Prod.fst hww')
      simpa only [wit] using this
    have hw1 := congrArg Prod.snd hww'
    have hi : (pr w).1 = (pr w').1 := by
      have := congrArg Fin.val (congrArg Prod.fst hw1)
      simpa only [wit] using this
    have hs : (pr w).2 = (pr w').2 := by
      have := congrArg Fin.val (congrArg Prod.snd hw1)
      simpa only [wit] using this
    have hs2 : ((pr w).2 : ZMod p) = ((pr w').2 : ZMod p) := by rw [hs]
    have hi2 : ((pr w).1 : ZMod p) = ((pr w').1 : ZMod p) := by rw [hi]
    have hd_eq : w.1.2 = w'.1.2 := by
      rw [hs2] at hq2
      exact mul_left_cancel₀ (hnonzero w') hq2
    have ha_eq : w.1.1 = w'.1.1 := by
      rw [hd_eq, hi2] at hq1
      exact add_right_cancel hq1
    exact Subtype.ext (Prod.ext ha_eq hd_eq)
  have hwit_ap : ∀ w : {w : ZMod p × ZMod p // w ∈ Good}, (wit w).1 ∈ APs := by
    intro w
    rw [hAPs, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hwW : w.1 ∈ W := hGood_sub w.2
      have hwD : w.1.2 ∈ D := by rw [hW, Finset.mem_product] at hwW; exact hwW.2
      have hw2 : w.1.2 ≠ 0 := by rw [hD, Finset.mem_erase] at hwD; exact hwD.1
      simpa only [wit] using mul_ne_zero (hnonzero w) hw2
    · intro j hj
      have hmem := (hpr w).2.2.2 j hj
      rw [hpos, Finset.mem_filter] at hmem
      simp only [wit]
      have heq : w.1.1 + ((pr w).1 : ZMod p) * w.1.2 + (j : ZMod p) * (((pr w).2 : ZMod p) * w.1.2)
          = w.1.1 + (((pr w).1 + (pr w).2 * j : ℕ) : ZMod p) * w.1.2 := by
        push_cast; ring
      rw [heq]
      exact hmem.2
  have hsub : (Good.attach.image wit) ⊆ APs ×ˢ (Finset.univ : Finset (Fin M × Fin M)) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Finset.mem_product]
    exact ⟨hwit_ap w, Finset.mem_univ _⟩
  have hE : (Good.card : ℝ) ≤ (APs.card : ℝ) * (M:ℝ) * (M:ℝ) := by
    have h1 : (Good.attach.image wit).card = Good.attach.card :=
      Finset.card_image_of_injOn (fun a _ b _ h => hwit_inj h)
    have h2 : (Good.attach.image wit).card ≤
        (APs ×ˢ (Finset.univ : Finset (Fin M × Fin M))).card := Finset.card_le_card hsub
    have h2' : (Good.attach.image wit).card ≤ APs.card * (M * M) := by
      simp only [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h2
      exact h2
    calc (Good.card : ℝ) = (Good.attach.card : ℝ) := by rw [Finset.card_attach]
      _ = ((Good.attach.image wit).card : ℝ) := by rw [h1]
      _ ≤ ((APs.card * (M * M) : ℕ) : ℝ) := by exact_mod_cast h2'
      _ = (APs.card : ℝ) * (M:ℝ) * (M:ℝ) := by push_cast; ring
  have hAPscard_goal : (θ / (4 * (M:ℝ)^2)) * (p:ℝ)^2 ≤ (APs.card : ℝ) := by
    have hp21 : (p:ℝ) - 1 ≥ (p:ℝ)/2 := by linarith
    have h4 : (0:ℝ) < 4 * (M:ℝ)^2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ h4]
    nlinarith [hE, hGood_lb, hp21, hθ]
  rw [hAPs] at hAPscard_goal
  exact hAPscard_goal


theorem many_aps_of_prime_engine_function
    (hengine : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ P : ℕ, ∀ (p : ℕ) [NeZero p], Nat.Prime p → P ≤ p →
      ∀ A : Finset (ZMod p), δ * (p : ℝ) ≤ (A.card : ℝ) →
        ∃ a b : ZMod p, b ≠ 0 ∧ ∀ j : ℕ, j < k → a + (j : ZMod p) * b ∈ A) :
    ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∃ P : ℕ,
      ∀ (p : ℕ) [NeZero p], Nat.Prime p → P ≤ p →
      ∀ f : ZMod p → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) → δ * (p : ℝ) ≤ ∑ x, f x →
        c * (p : ℝ) ^ 2 ≤ ∑ x : ZMod p, ∑ r : ZMod p,
          ∏ j ∈ Finset.range k, f (x + (j : ZMod p) * r) := by
  intro k hk δ hδ
  have eng : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ P : ℕ, ∀ p : ℕ, Nat.Prime p → P ≤ p →
      ∀ A : Finset (ZMod p), δ * (p : ℝ) ≤ (A.card : ℝ) →
        ∃ a b : ZMod p, b ≠ 0 ∧ ∀ j : ℕ, j < k → a + (j : ZMod p) * b ∈ A := by
    intro k δ hδ
    obtain ⟨P, hP⟩ := hengine k δ hδ
    exact ⟨P, fun p hp hPp A hA => by
      haveI : NeZero p := ⟨hp.ne_zero⟩
      exact hP p hp hPp A hA⟩
  have hfin := Commons.Combinatorics.Additive.Szemeredi.finite_of_prime_engine eng
  by_cases hδ1 : δ ≤ 1
  · set θ : ℝ := δ/2 with hθdef
    have hθpos : 0 < θ := by rw [hθdef]; linarith
    have hθ1 : θ ≤ 1 := by rw [hθdef]; linarith
    obtain ⟨N0, hN0⟩ := hfin k (θ/2) (by positivity)
    set M : ℕ := max N0 1 with hMdef
    have hM1 : 1 ≤ M := le_max_right _ _
    have hint : ∀ S : Finset ℕ, S ⊆ Finset.range M → (θ/2) * (M:ℝ) ≤ (S.card:ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b*j ∈ S := by
      intro S hS hSc
      exact hN0 M (le_max_left _ _) S hS hSc
    refine ⟨θ^k * (θ / (4 * (M:ℝ)^2)), by positivity, max M 2, ?_⟩
    intro p _ hp hPp f hf0 hf1 hfmass
    have hMp : M ≤ p := le_trans (le_max_left _ _) hPp
    have h2p : 2 ≤ p := le_trans (le_max_right _ _) hPp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) h2p)
    set A : Finset (ZMod p) := (Finset.univ : Finset (ZMod p)).filter (fun x => θ ≤ f x) with hAdef
    set B : Finset (ZMod p) := (Finset.univ : Finset (ZMod p)).filter (fun x => ¬(θ ≤ f x)) with hBdef
    have hsplit : ∑ x : ZMod p, f x = ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
      rw [hAdef, hBdef]
      exact (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (ZMod p)))
        (p := fun x => θ ≤ f x) (f := f)).symm
    have hAcard : θ * (p:ℝ) ≤ (A.card:ℝ) := by
      have hb1 : ∑ x ∈ A, f x ≤ (A.card : ℝ) := by
        calc ∑ x ∈ A, f x ≤ ∑ _x ∈ A, (1:ℝ) := Finset.sum_le_sum (fun x _ => hf1 x)
          _ = (A.card:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hb2 : ∑ x ∈ B, f x ≤ (B.card:ℝ) * θ := by
        have hle : ∀ x ∈ B, f x ≤ θ := by
          intro x hx
          rw [hBdef, Finset.mem_filter] at hx
          exact le_of_lt (not_le.mp hx.2)
        calc ∑ x ∈ B, f x ≤ ∑ _x ∈ B, θ := Finset.sum_le_sum hle
          _ = (B.card:ℝ) * θ := by rw [Finset.sum_const, nsmul_eq_mul]
      have hcardAB : (A.card:ℝ) + (B.card:ℝ) = (p:ℝ) := by
        have h := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (ZMod p))) (p := fun x => θ ≤ f x)
        rw [Finset.card_univ, ZMod.card] at h
        rw [hAdef, hBdef]
        rw [← Nat.cast_add, h]
      have hmass : δ * (p:ℝ) ≤ ∑ x ∈ A, f x + ∑ x ∈ B, f x := by rw [← hsplit]; exact hfmass
      have hδ2θ : δ = 2*θ := by rw [hθdef]; ring
      have hAcardp : (A.card:ℝ) ≤ (p:ℝ) := by
        rw [← hcardAB]
        linarith [Nat.cast_nonneg (α := ℝ) B.card]
      nlinarith [hmass, hb1, hb2, hcardAB, hAcardp, hθ1, hθpos, hδ2θ]
    have hcount := varnavides_count k hk M hM1 θ hθpos hθ1 hint p hp hMp A hAcard
    set APs : Finset (ZMod p × ZMod p) := (Finset.univ : Finset (ZMod p × ZMod p)).filter
      (fun q => q.2 ≠ 0 ∧ ∀ j : ℕ, j < k → q.1 + (j : ZMod p) * q.2 ∈ A) with hAPs
    have hcount' : (θ / (4 * (M:ℝ)^2)) * (p:ℝ)^2 ≤ (APs.card : ℝ) := by
      rw [hAPs]; exact hcount
    let gp : ZMod p × ZMod p → ℝ :=
      fun q => ∏ j ∈ Finset.range k, f (q.1 + (j : ZMod p) * q.2)
    have hgp_nonneg : ∀ q, 0 ≤ gp q := fun q => Finset.prod_nonneg (fun j _ => hf0 _)
    have hS : (∑ x : ZMod p, ∑ r : ZMod p, ∏ j ∈ Finset.range k, f (x + (j : ZMod p) * r))
        = ∑ q ∈ (Finset.univ : Finset (ZMod p)) ×ˢ (Finset.univ : Finset (ZMod p)), gp q := by
      rw [Finset.sum_product]
    have h1 : ∑ q ∈ APs, gp q
        ≤ ∑ q ∈ (Finset.univ : Finset (ZMod p)) ×ˢ (Finset.univ : Finset (ZMod p)), gp q :=
      Finset.sum_le_sum_of_subset_of_nonneg (s := APs)
        (t := (Finset.univ : Finset (ZMod p)) ×ˢ (Finset.univ : Finset (ZMod p)))
        (by rw [hAPs]; exact Finset.filter_subset _ _) (fun q _ _ => hgp_nonneg q)
    have h2 : (APs.card : ℝ) * θ^k ≤ ∑ q ∈ APs, gp q := by
      have hf : ∀ q ∈ APs, θ^k ≤ gp q := by
        intro q hq
        rw [hAPs, Finset.mem_filter] at hq
        obtain ⟨_, hqA⟩ := hq
        calc θ^k = ∏ j ∈ Finset.range k, θ := by rw [Finset.prod_const, Finset.card_range]
          _ ≤ ∏ j ∈ Finset.range k, f (q.1 + (j : ZMod p) * q.2) := by
              apply Finset.prod_le_prod
              · intro j _; exact le_of_lt hθpos
              · intro j hj
                have := hqA.2 j (Finset.mem_range.mp hj)
                rw [hAdef, Finset.mem_filter] at this
                exact this.2
      calc (APs.card : ℝ) * θ^k = ∑ _q ∈ APs, θ^k := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ q ∈ APs, gp q := Finset.sum_le_sum hf
    have hgoal : (θ^k * (θ / (4 * (M:ℝ)^2))) * (p:ℝ)^2
        ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ j ∈ Finset.range k, f (x + (j : ZMod p) * r) := by
      have hk0 : (0:ℝ) ≤ θ^k := by positivity
      calc (θ^k * (θ / (4 * (M:ℝ)^2))) * (p:ℝ)^2
          = θ^k * ((θ / (4 * (M:ℝ)^2)) * (p:ℝ)^2) := by ring
        _ ≤ θ^k * (APs.card : ℝ) := mul_le_mul_of_nonneg_left hcount' hk0
        _ = (APs.card : ℝ) * θ^k := by ring
        _ ≤ ∑ q ∈ APs, gp q := h2
        _ ≤ ∑ q ∈ (Finset.univ : Finset (ZMod p)) ×ˢ (Finset.univ : Finset (ZMod p)), gp q := h1
        _ = ∑ x : ZMod p, ∑ r : ZMod p, ∏ j ∈ Finset.range k, f (x + (j : ZMod p) * r) := hS.symm
    exact hgoal
  · push Not at hδ1
    refine ⟨1, one_pos, 0, ?_⟩
    intro p _ hp _ f hf0 hf1 hfmass
    have hple : ∑ x : ZMod p, f x ≤ (p:ℝ) := by
      calc ∑ x : ZMod p, f x ≤ ∑ _x : ZMod p, (1:ℝ) := Finset.sum_le_sum (fun x _ => hf1 x)
        _ = (p:ℝ) := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
    have hle1 : δ ≤ 1 := le_of_mul_le_mul_right (by linarith [hfmass, hple] : δ * (p:ℝ) ≤ 1 * (p:ℝ)) hp0
    linarith

end Commons.Combinatorics.Additive.Szemeredi
