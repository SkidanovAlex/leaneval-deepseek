import Mathlib
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.SumDefs
import Submission.Work.HP.NA.card_primMod
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.NA.card_pair_kernel_le_gen
import Submission.Work.HP.NA.gcd_veronese_gcd_pow
import Submission.Work.HP.NA.sum_gcd_int_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open Finset
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.HP
namespace NA

/-- Double counting: the sum of the squares of `β`-indicator sums equals the sum over ordered
pairs `(b₁,b₂)` of the number of `a ∈ A` satisfying both conditions. -/
theorem sum_sq_indicator {α β : Type*} [Fintype α] [Fintype β]
    (A : Finset α) (B : Finset β) (f : α → β → Prop) [DecidableRel f] :
    (∑ a ∈ A, (∑ b ∈ B, (if f a b then (1 : ℝ) else 0)) ^ 2)
      = ∑ b1 ∈ B, ∑ b2 ∈ B, ((A.filter (fun a => f a b1 ∧ f a b2)).card : ℝ) := by
  have hmul : ∀ a, (∑ b ∈ B, (if f a b then (1 : ℝ) else 0)) ^ 2
      = ∑ b1 ∈ B, ∑ b2 ∈ B,
          (if f a b1 then (1 : ℝ) else 0) * (if f a b2 then (1 : ℝ) else 0) := by
    intro a
    rw [pow_two, Finset.sum_mul_sum]
  simp_rw [hmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b1 _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b2 _ => ?_)
  have hcongr : ∀ a, (if f a b1 then (1 : ℝ) else 0) * (if f a b2 then (1 : ℝ) else 0)
      = (if f a b1 ∧ f a b2 then (1 : ℝ) else 0) := by
    intro a
    by_cases h1 : f a b1 <;> by_cases h2 : f a b2 <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun a _ => hcongr a)]
  rw [Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun a _ => by by_cases h : f a b1 ∧ f a b2 <;> simp [h])


/-- `Set.ncard` of a decidable predicate set on a finite type is the sum of the indicator. -/
theorem ncard_setOf {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Set.ncard {x | p x} = (Finset.univ.filter p).card := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext x
  simp

/-- `sigQ` as a normalised count over `Bprim`. -/
theorem sigQ_eq (d n Q : ℕ) [NeZero Q] (a : Mon d n → ZMod Q) :
    sigQ d n Q a = ((Bprim n Q).filter (fun b => fev d n a b = 0)).card / (Q : ℝ) ^ n := by
  classical
  have h1 : Set.ncard {b : Fin (n + 1) → ZMod Q | IsPrimGen Q b ∧ fev d n a b = 0}
      = ((Bprim n Q).filter (fun b => fev d n a b = 0)).card := by
    rw [ncard_setOf (p := fun b => IsPrimGen Q b ∧ fev d n a b = 0)]
    congr 1
    rw [Bprim, Finset.filter_filter]
  unfold sigQ
  exact congrArg (fun k : ℕ => (k : ℝ) / (Q : ℝ) ^ n) h1

/-- The Veronese image of the integer representative of `b` reduces to the Veronese image of `b`. -/
theorem veronese_irep_cast {d n q : ℕ} [NeZero q] (b : Fin (n + 1) → ZMod q) (m : Mon d n) :
    ((veronese d n (irep b) m : ℤ) : ZMod q) = veronese d n b m := by
  simp only [veronese]
  have h : ((∏ i, (irep b i) ^ ((m.1 i : ℕ)) : ℤ) : ZMod q)
      = ∏ i, (((irep b i) : ℤ) : ZMod q) ^ ((m.1 i : ℕ)) := by
    push_cast
    rfl
  rw [h]
  exact Finset.prod_congr rfl (fun i _ => by rw [irep_cast])

/-- `veronese` at the single-variable monomial `Xᵢ^d` (generic coefficient ring). -/
theorem veronese_monDi' {R : Type*} [CommSemiring R] (d n : ℕ) (x : Fin (n + 1) → R)
    (i : Fin (n + 1)) : veronese d n x (monDi d n i) = x i ^ d := by
  simp only [veronese, monDi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The kernel bound for a pair of primitive vectors. -/
theorem kern_le {d n p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) [NeZero (p ^ r)]
    (b1 b2 : Fin (n + 1) → ZMod (p ^ r)) (hb1 : b1 ∈ Bprim n (p ^ r)) :
    Nat.card {a : Mon d n → ZMod (p ^ r) // fev d n a b1 = 0 ∧ fev d n a b2 = 0}
      ≤ (p ^ r) ^ (NN d n - 2) *
        Nat.gcd (gcdMinors2 (veronese d n (irep b1)) (veronese d n (irep b2))).natAbs
          (p ^ r) := by
  classical
  have hb1' : IsPrimGen (p ^ r) b1 := mem_Bprim.mp hb1
  have hunit : ∃ i, IsUnit (b1 i) :=
    (isPrimMod_iff_exists_isUnit p r (n + 1) hp hr b1).mp hb1'
  obtain ⟨j0, hj0⟩ := hunit
  have hu : ∃ i, IsUnit (((veronese d n (irep b1)) i : ℤ) : ZMod (p ^ r)) := by
    refine ⟨monDi d n j0, ?_⟩
    rw [veronese_irep_cast, veronese_monDi']
    exact hj0.pow d
  have heq : ∀ a : Mon d n → ZMod (p ^ r),
      (fev d n a b1 = 0 ∧ fev d n a b2 = 0) ↔
      ((∑ i, a i * ((veronese d n (irep b1) i : ℤ) : ZMod (p ^ r))) = 0 ∧
       (∑ i, a i * ((veronese d n (irep b2) i : ℤ) : ZMod (p ^ r))) = 0) := by
    intro a
    have h1 : fev d n a b1 = ∑ i, a i * ((veronese d n (irep b1) i : ℤ) : ZMod (p ^ r)) := by
      rw [fev]; exact Finset.sum_congr rfl (fun m _ => by rw [veronese_irep_cast])
    have h2 : fev d n a b2 = ∑ i, a i * ((veronese d n (irep b2) i : ℤ) : ZMod (p ^ r)) := by
      rw [fev]; exact Finset.sum_congr rfl (fun m _ => by rw [veronese_irep_cast])
    rw [h1, h2]
  calc Nat.card {a : Mon d n → ZMod (p ^ r) // fev d n a b1 = 0 ∧ fev d n a b2 = 0}
      = Nat.card {a : Mon d n → ZMod (p ^ r) //
          (∑ i, a i * ((veronese d n (irep b1) i : ℤ) : ZMod (p ^ r))) = 0 ∧
          (∑ i, a i * ((veronese d n (irep b2) i : ℤ) : ZMod (p ^ r))) = 0} :=
        Nat.card_congr (Equiv.subtypeEquivRight heq)
    _ ≤ (p ^ r) ^ (Fintype.card (Mon d n) - 2) *
          Nat.gcd (gcdMinors2 (veronese d n (irep b1)) (veronese d n (irep b2))).natAbs
            (p ^ r) :=
        card_pair_kernel_le_gen hp hr _ _ hu
    _ = (p ^ r) ^ (NN d n - 2) *
          Nat.gcd (gcdMinors2 (veronese d n (irep b1)) (veronese d n (irep b2))).natAbs
            (p ^ r) := rfl

/-- `(s.filter p).card` is bounded by the cardinality of the subtype of elements satisfying `p`. -/
theorem card_filter_le_natCard {α : Type*} [Fintype α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] : (s.filter p).card ≤ Nat.card {x // p x} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.card_le_card (fun x hx => by
    rw [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, hx.2⟩)

/-- A primitive vector has a coordinate whose integer representative is not divisible by `p`. -/
theorem exists_not_dvd_irep_of_mem_Bprim {n p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) [NeZero (p ^ r)]
    {b : Fin (n + 1) → ZMod (p ^ r)} (hb : b ∈ Bprim n (p ^ r)) :
    ∃ i, ¬ (p : ℤ) ∣ irep b i := by
  classical
  have hb' : IsPrimGen (p ^ r) b := mem_Bprim.mp hb
  obtain ⟨i, hi⟩ := (isPrimMod_iff_exists_isUnit p r (n + 1) hp hr b).mp hb'
  refine ⟨i, ?_⟩
  simp only [irep_apply]
  have hnotdvd : ¬ p ∣ (b i).val := by
    have h' : IsUnit (((b i).val : ℕ) : ZMod (p ^ r)) := by rwa [ZMod.natCast_zmod_val]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mp h'
  intro hdvd
  exact hnotdvd (by exact_mod_cast hdvd)

/-- `NN d n ≥ 2` when `d, n ≥ 2`. -/
theorem two_le_NN (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) : 2 ≤ NN d n := by
  have h2n : 2 ≤ n + 1 := by omega
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  have hne : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  have hdiff : monDi d n i0 ≠ monDi d n i1 := by
    intro h
    have h2 : ((monDi d n i0).1 i1 : ℕ) = ((monDi d n i1).1 i1 : ℕ) :=
      congrArg (fun m : Mon d n => ((m.1 i1 : Fin (d + 1)) : ℕ)) h
    simp only [monDi, Fin.val_mk] at h2
    rw [if_neg hne] at h2
    have : (0 : ℕ) = d := by simpa using h2
    omega
  have hinj : Function.Injective
      (fun k : Fin 2 => if k = 0 then monDi d n i0 else monDi d n i1) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have h := Fintype.card_le_of_injective
    (fun k : Fin 2 => if k = 0 then monDi d n i0 else monDi d n i1) hinj
  simpa using h

/-- The gcd of the `2×2` minors of the pair `(ν(repr b₁), ν(repr b₂))`. -/
def Gvero (d n p r : ℕ) (b1 b2 : Fin (n + 1) → ZMod (p ^ r)) : ℕ :=
  Nat.gcd (gcdMinors2 (veronese d n (irep b1)) (veronese d n (irep b2))).natAbs (p ^ r)

/-- The gcd of the `2×2` minors of the pair `(repr b₁, repr b₂)`. -/
def Gint (n p r : ℕ) (b1 b2 : Fin (n + 1) → ZMod (p ^ r)) : ℕ :=
  Nat.gcd (gcdMinors2 (irep b1) (irep b2)).natAbs (p ^ r)

theorem sum_sigQ_sq_bound (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p r : ℕ) [NeZero (p ^ r)], p.Prime → 1 ≤ r →
      (∑ a ∈ Work.HP.NA.primFinset d n (p ^ r), (Work.HP.NA.sigQ d n (p ^ r) a) ^ 2)
        ≤ (p : ℝ) ^ (r * Work.HP.NN d n) * (1 + C / (p : ℝ) ^ (n - 1)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro p r hNe hp hr
  classical
  set A : Finset (Mon d n → ZMod (p ^ r)) := primFinset d n (p ^ r) with hA
  set B : Finset (Fin (n + 1) → ZMod (p ^ r)) := Bprim n (p ^ r) with hB
  have hpr2 : 2 ≤ p ^ r := by
    calc (2 : ℕ) ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos hr
  have hN2 : 2 ≤ NN d n := two_le_NN d n hd hn
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < (p : ℝ) ^ r := pow_pos hpR r
  have hq0 : ((p : ℝ) ^ r) ≠ 0 := ne_of_gt hqR
  set den : ℝ := (((p ^ r : ℕ) : ℝ)) ^ n with hcdef
  have hσ : ∀ a : Mon d n → ZMod (p ^ r),
      sigQ d n (p ^ r) a = ((B.filter (fun b => fev d n a b = 0)).card : ℝ) / den := by
    intro a
    rw [hcdef, sigQ_eq, ← hB]
  have hmain1 : (∑ a ∈ A, (sigQ d n (p ^ r) a) ^ 2)
      = (∑ a ∈ A, ((B.filter (fun b => fev d n a b = 0)).card : ℝ) ^ 2) / den ^ 2 := by
    have h1 : ∀ a : Mon d n → ZMod (p ^ r),
        (sigQ d n (p ^ r) a) ^ 2
          = ((B.filter (fun b => fev d n a b = 0)).card : ℝ) ^ 2 / den ^ 2 := by
      intro a; rw [hσ a, div_pow]
    rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_div]
  have hcard : (∑ a ∈ A, ((B.filter (fun b => fev d n a b = 0)).card : ℝ) ^ 2)
      = ∑ b1 ∈ B, ∑ b2 ∈ B,
          ((A.filter (fun a => fev d n a b1 = 0 ∧ fev d n a b2 = 0)).card : ℝ) := by
    have hc : ∀ a : Mon d n → ZMod (p ^ r),
        ((B.filter (fun b => fev d n a b = 0)).card : ℝ)
          = ∑ b ∈ B, (if fev d n a b = 0 then (1 : ℝ) else 0) := by
      intro a
      rw [Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun b _ => by by_cases h : fev d n a b = 0 <;> simp [h])
    simp only [hc]
    exact sum_sq_indicator A B (fun a b => fev d n a b = 0)
  have hpair : ∀ b1 ∈ B, ∀ b2 ∈ B,
      (A.filter (fun a => fev d n a b1 = 0 ∧ fev d n a b2 = 0)).card
        ≤ (p ^ r) ^ (NN d n - 2) * Gvero d n p r b1 b2 := by
    intro b1 hb1 b2 hb2
    have hb1' : b1 ∈ Bprim n (p ^ r) := by simpa only [hB] using hb1
    calc (A.filter (fun a => fev d n a b1 = 0 ∧ fev d n a b2 = 0)).card
        ≤ Nat.card {a : Mon d n → ZMod (p ^ r) //
            fev d n a b1 = 0 ∧ fev d n a b2 = 0} :=
          card_filter_le_natCard A _
      _ ≤ (p ^ r) ^ (NN d n - 2) * Gvero d n p r b1 b2 := by
          simpa only [Gvero] using kern_le hp hr b1 b2 hb1'
  have hgj : ∀ b1 ∈ B, ∀ b2 ∈ B,
      (Gvero d n p r b1 b2 : ℝ) = (Gint n p r b1 b2 : ℝ) := by
    intro b1 hb1 b2 hb2
    have hb1' : b1 ∈ Bprim n (p ^ r) := by simpa only [hB] using hb1
    have hb2' : b2 ∈ Bprim n (p ^ r) := by simpa only [hB] using hb2
    simp only [Gvero, Gint]
    rw [gcd_veronese_gcd_pow d n p r (by omega) hp (irep b1) (irep b2)
      (exists_not_dvd_irep_of_mem_Bprim hp hr hb1')
      (exists_not_dvd_irep_of_mem_Bprim hp hr hb2')]
  have hS : (∑ b1 ∈ B, ∑ b2 ∈ B, (Gint n p r b1 b2 : ℝ))
      ≤ (p : ℝ) ^ (2 * (r * (n + 1))) * (1 + 4 / (p : ℝ) ^ (n - 1)) := by
    simpa only [Gint] using sum_gcd_int_le n p r hn hp hr
  have hbound : (∑ a ∈ A, ((B.filter (fun b => fev d n a b = 0)).card : ℝ) ^ 2)
      ≤ (((p ^ r : ℕ) : ℝ)) ^ (NN d n - 2) *
          ((p : ℝ) ^ (2 * (r * (n + 1))) * (1 + 4 / (p : ℝ) ^ (n - 1))) := by
    rw [hcard]
    calc (∑ b1 ∈ B, ∑ b2 ∈ B,
            ((A.filter (fun a => fev d n a b1 = 0 ∧ fev d n a b2 = 0)).card : ℝ))
        ≤ ∑ b1 ∈ B, ∑ b2 ∈ B,
            (((p ^ r) ^ (NN d n - 2) * Gvero d n p r b1 b2 : ℕ) : ℝ) := by
          apply Finset.sum_le_sum; intro b1 hb1
          apply Finset.sum_le_sum; intro b2 hb2
          exact_mod_cast hpair b1 hb1 b2 hb2
      _ = (((p ^ r : ℕ) : ℝ)) ^ (NN d n - 2) *
            (∑ b1 ∈ B, ∑ b2 ∈ B, (Gvero d n p r b1 b2 : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b1 _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b2 _
          simp only [Nat.cast_mul, Nat.cast_pow]
      _ = (((p ^ r : ℕ) : ℝ)) ^ (NN d n - 2) *
            (∑ b1 ∈ B, ∑ b2 ∈ B, (Gint n p r b1 b2 : ℝ)) := by
          congr 1
          apply Finset.sum_congr rfl; intro b1 hb1
          apply Finset.sum_congr rfl; intro b2 hb2
          exact hgj b1 hb1 b2 hb2
      _ ≤ (((p ^ r : ℕ) : ℝ)) ^ (NN d n - 2) *
            ((p : ℝ) ^ (2 * (r * (n + 1))) * (1 + 4 / (p : ℝ) ^ (n - 1))) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
  have harith : ((((p ^ r : ℕ) : ℝ)) ^ (NN d n - 2) *
        ((p : ℝ) ^ (2 * (r * (n + 1))) * (1 + 4 / (p : ℝ) ^ (n - 1)))) / den ^ 2
      = (p : ℝ) ^ (r * NN d n) * (1 + 4 / (p : ℝ) ^ (n - 1)) := by
    rw [hcdef, Nat.cast_pow]
    have hB2 : (p : ℝ) ^ (2 * (r * (n + 1))) = ((p : ℝ) ^ r) ^ (2 * (n + 1)) := by
      rw [show 2 * (r * (n + 1)) = r * (2 * (n + 1)) by ring, pow_mul]
    have hDen : (((p : ℝ) ^ r) ^ n) ^ 2 = ((p : ℝ) ^ r) ^ (2 * n) := by
      rw [pow_two, ← pow_add]; congr 1; ring
    have hRHS : (p : ℝ) ^ (r * NN d n) = ((p : ℝ) ^ r) ^ (NN d n) := by rw [pow_mul]
    rw [hB2, hDen, hRHS]
    have step1 : ((p : ℝ) ^ r) ^ (NN d n - 2) * (((p : ℝ) ^ r) ^ (2 * (n + 1)) *
          (1 + 4 / (p : ℝ) ^ (n - 1)))
        = ((p : ℝ) ^ r) ^ (NN d n + 2 * n) * (1 + 4 / (p : ℝ) ^ (n - 1)) := by
      rw [← mul_assoc, ← pow_add,
        show NN d n - 2 + 2 * (n + 1) = NN d n + 2 * n by omega]
    rw [step1, pow_add, div_eq_iff (pow_ne_zero _ hq0)]
    ring
  calc (∑ a ∈ A, (sigQ d n (p ^ r) a) ^ 2)
      = (∑ a ∈ A, ((B.filter (fun b => fev d n a b = 0)).card : ℝ) ^ 2) / den ^ 2 := hmain1
    _ ≤ ((((p ^ r : ℕ) : ℝ)) ^ (NN d n - 2) *
          ((p : ℝ) ^ (2 * (r * (n + 1))) * (1 + 4 / (p : ℝ) ^ (n - 1)))) / den ^ 2 :=
        div_le_div_of_nonneg_right hbound (sq_nonneg den)
    _ = (p : ℝ) ^ (r * NN d n) * (1 + 4 / (p : ℝ) ^ (n - 1)) := harith

end NA
end Work.HP
