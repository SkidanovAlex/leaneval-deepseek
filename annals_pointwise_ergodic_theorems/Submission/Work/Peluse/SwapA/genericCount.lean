import Mathlib
import Submission.Work.Peluse.SwapA.evalPairFiber
import Submission.Work.Peluse.SwapA.cardSmallQOf
import Submission.Work.Peluse.SwapA.cardDvdQOf

/-!
# (GEN) Genericity count for the slopes of the regime swap

The proof has two halves.

* **Per slot.**  If `ε ≠ ε'` are the two sign patterns of a ladder slot `k` (they differ at the
  pivot, `slotAt_ne`), the plugs `ι ε`, `ι ε'` are independent and uniform over `Plug t H`, so the
  number of `ι` failing `genPair H η` at `k` is `#(bad plug pairs) · #ι / #Plug²` (`evalPairFiber`).
  The bad pairs are counted in `card_badPairs`: the two magnitude conditions by `cardSmallQOf` and
  the `gcd`-condition by the union bound over divisors `M < d ≤ tH` together with `cardDvdQOf`.
* **Union bound.**  The `∃ k` condition is the union over the `slotCard (2^t - 1)` slots; summing
  the per-slot bound gives the constant `slotCard (2^t - 1) · (8 + 2t)`, rounded up below.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace Work.Peluse.SwapA

noncomputable section
open Work.Peluse

open Classical in
/-- The plug pairs whose slopes fail `genPair`: this is the set counted at a single slot. -/
def badPairs {t H : ℕ} (ω : Fin t → Bool) (η : ℝ) : Finset (Plug t H × Plug t H) :=
  Finset.univ.filter (fun p : Plug t H × Plug t H =>
    ¬ LadderP.Swap.genPair H η (qOf ω p.1) (qOf ω p.2))

/-- The "slot `k` fails" predicate of the genericity count. -/
def slotBad {t H : ℕ} (η : ℝ) (k : Fin (LadderP.Swap.slotCard (2 ^ t - 1)))
    (ι : (Fin (2 ^ t - 1) → Bool) → Plug t H) : Prop :=
  ¬ LadderP.Swap.genPair H η
    (qOf (Holds.omegaOf t (LadderP.Swap.slotAt (2 ^ t - 1) k).1)
      (ι (LadderP.Swap.slotAt (2 ^ t - 1) k).2.1))
    (qOf (Holds.omegaOf t (LadderP.Swap.slotAt (2 ^ t - 1) k).1)
      (ι (LadderP.Swap.slotAt (2 ^ t - 1) k).2.2))

/-- Membership in `badPairs` is exactly the failure of `genPair` at the plug pair. -/
lemma slotBad_iff {t H : ℕ} {η : ℝ} {k : Fin (LadderP.Swap.slotCard (2 ^ t - 1))}
    {ι : (Fin (2 ^ t - 1) → Bool) → Plug t H} :
    slotBad η k ι ↔
      (ι (LadderP.Swap.slotAt (2 ^ t - 1) k).2.1, ι (LadderP.Swap.slotAt (2 ^ t - 1) k).2.2)
        ∈ badPairs (t := t) (H := H) (Holds.omegaOf t (LadderP.Swap.slotAt (2 ^ t - 1) k).1) η := by
  classical
  rw [slotBad, badPairs, Finset.mem_filter]
  exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩

open Classical in
/-- **(pair count)** For a nonzero sign pattern `ω`, the number of plug pairs `(p,q)` whose slopes
`ω·(p.1−p.2)` and `ω·(q.1−q.2)` fail `genPair H η` is at most `(8+2t)(η + 1/H)·#Plug²`. -/
theorem card_badPairs {t H : ℕ} (ht : 1 ≤ t) (hH : 1 ≤ H) (ω : Fin t → Bool) (hω : ω ≠ 0)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ((Finset.univ.filter (fun p : Plug t H × Plug t H =>
        ¬ LadderP.Swap.genPair H η (qOf ω p.1) (qOf ω p.2))).card : ℝ)
      ≤ (8 + 2 * (t : ℝ)) * (η + 1 / (H : ℝ)) * (Fintype.card (Plug t H) : ℝ) ^ 2 := by
  classical
  have hη0' : 0 ≤ η := hη0.le
  have hSmall : ∀ {η' : ℝ}, 0 ≤ η' →
      ((Finset.univ.filter (fun v : Plug t H => |qOf ω v| < η' * (H : ℝ))).card : ℝ)
        ≤ (2 * η' + 1 / (H : ℝ)) * (Fintype.card (Plug t H) : ℝ) :=
    fun {η'} hη' => cardSmallQOf ht hH ω hω hη'
  have hDvd : ∀ d : ℕ, 1 ≤ d →
      ((Finset.univ.filter (fun v : Plug t H => (d : ℤ) ∣ qOf ω v)).card : ℝ)
        ≤ (1 / (d : ℝ) + 1 / (H : ℝ)) * (Fintype.card (Plug t H) : ℝ) :=
    fun d hd => cardDvdQOf ht hH hd ω hω
  set K : ℝ := (Fintype.card (Plug t H) : ℝ)
  have hK0 : 0 ≤ K := by positivity
  set S : Finset (Plug t H × Plug t H) := Finset.univ.filter (fun p : Plug t H × Plug t H =>
        ¬ LadderP.Swap.genPair H η (qOf ω p.1) (qOf ω p.2))
  set A1 : Finset (Plug t H × Plug t H) :=
    Finset.univ.filter (fun p : Plug t H × Plug t H => |qOf ω p.1| < η * (H:ℝ))
  set A2 : Finset (Plug t H × Plug t H) :=
    Finset.univ.filter (fun p : Plug t H × Plug t H => |qOf ω p.2| < η * (H:ℝ))
  set A3 : Finset (Plug t H × Plug t H) :=
    Finset.univ.filter (fun p : Plug t H × Plug t H =>
      1/η < ((Int.gcd (qOf ω p.1) (qOf ω p.2) : ℕ) : ℝ))
  -- (a) decomposition
  have hsub : S ⊆ (A1 ∪ A2) ∪ A3 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hbad := hp.2
    rw [LadderP.Swap.genPair] at hbad
    by_cases h1 : η * (H:ℝ) ≤ ((|qOf ω p.1| : ℤ) : ℝ)
    · by_cases h2 : η * (H:ℝ) ≤ ((|qOf ω p.2| : ℤ) : ℝ)
      · have h3 : 1/η < ((Int.gcd (qOf ω p.1) (qOf ω p.2) : ℕ) : ℝ) := by
          by_contra hc
          push Not at hc
          exact hbad ⟨h1, h2, hc⟩
        exact Finset.mem_union_right (A1 ∪ A2) (by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h3⟩)
      · push Not at h2
        exact Finset.mem_union_left A3 (Finset.mem_union_right A1 (by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h2⟩))
    · push Not at h1
      exact Finset.mem_union_left A3 (Finset.mem_union_left A2 (by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h1⟩))
  -- (b) cardinality of the union
  have hcard : (S.card : ℝ) ≤ (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) := by
    have h1 : S.card ≤ ((A1 ∪ A2) ∪ A3).card := Finset.card_le_card hsub
    have h2 : ((A1 ∪ A2) ∪ A3).card ≤ A1.card + A2.card + A3.card := by
      have hu1 := Finset.card_union_le (A1 ∪ A2) A3
      have hu2 := Finset.card_union_le A1 A2
      omega
    calc (S.card : ℝ) ≤ (((A1 ∪ A2) ∪ A3).card : ℝ) := by exact_mod_cast h1
      _ ≤ ((A1.card + A2.card + A3.card : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) := by push_cast; ring
  -- (c) the two "small" pieces
  set B : Finset (Plug t H) := Finset.univ.filter (fun v : Plug t H => |qOf ω v| < η * (H:ℝ))
  have hBcard : (B.card : ℝ) ≤ (2*η + 1/(H:ℝ)) * K := hSmall hη0'
  have hKeq : (((Fintype.card (Plug t H)) : ℕ) : ℝ) = K := rfl
  have heq1 : A1 = B ×ˢ (Finset.univ : Finset (Plug t H)) := by
    ext p; simp [A1, B, Finset.mem_product]
  have heq2 : A2 = (Finset.univ : Finset (Plug t H)) ×ˢ B := by
    ext p; simp [A2, B, Finset.mem_product]
  have hA1card : (A1.card : ℝ) ≤ (2*η + 1/(H:ℝ)) * K * K := by
    rw [heq1, Finset.card_product, Finset.card_univ]
    push_cast
    rw [hKeq]
    nlinarith [hBcard, hK0]
  have hA2card : (A2.card : ℝ) ≤ (2*η + 1/(H:ℝ)) * K * K := by
    rw [heq2, Finset.card_product, Finset.card_univ]
    push_cast
    rw [hKeq]
    nlinarith [hBcard, hK0]
  -- (d) the gcd piece
  have hηpos : 0 < 1/η := by positivity
  set M : ℕ := ⌊1/η⌋₊
  set C : ℕ → Finset (Plug t H) := fun d => Finset.univ.filter (fun v : Plug t H => (d:ℤ) ∣ qOf ω v)
  have hMle : (M:ℝ) ≤ 1/η := Nat.floor_le hηpos.le
  have hMlt : 1/η < (M:ℝ) + 1 := by simpa [M] using Nat.lt_floor_add_one (1/η)
  have hA3sub : A3 ⊆ (Finset.Ioo M (t*H+1)).biUnion (fun d => C d ×ˢ C d) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp3 := hp.2
    set g : ℕ := Int.gcd (qOf ω p.1) (qOf ω p.2) with hg
    have hgM : M < g := by
      have hlt : (M:ℝ) < (g:ℝ) := lt_of_le_of_lt hMle hp3
      exact_mod_cast hlt
    have hb1 : (qOf ω p.1).natAbs ≤ t*H := by
      have habs := qOf_abs_le ω p.1
      have hcast : ((t*H : ℕ) : ℤ) = (t:ℤ)*(H:ℤ) := by push_cast; ring
      have h2 : (((qOf ω p.1).natAbs : ℤ)) ≤ ((t*H : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs, hcast]; exact habs
      exact_mod_cast h2
    have hb2 : (qOf ω p.2).natAbs ≤ t*H := by
      have habs := qOf_abs_le ω p.2
      have hcast : ((t*H : ℕ) : ℤ) = (t:ℤ)*(H:ℤ) := by push_cast; ring
      have h2 : (((qOf ω p.2).natAbs : ℤ)) ≤ ((t*H : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs, hcast]; exact habs
      exact_mod_cast h2
    have hgtH : g ≤ t*H := by
      rcases eq_or_ne (qOf ω p.2) 0 with hb | hb
      · rcases eq_or_ne (qOf ω p.1) 0 with ha | ha
        · have hg0 : g = 0 := by rw [hg, ha, hb]; simp [Int.gcd_zero_left]
          rw [hg0]; omega
        · exact le_trans (Int.gcd_le_natAbs_left (qOf ω p.2) ha) hb1
      · exact le_trans (Int.gcd_le_natAbs_right (qOf ω p.1) hb) hb2
    rw [Finset.mem_biUnion]
    refine ⟨g, ?_, ?_⟩
    · rw [Finset.mem_Ioo]; exact ⟨hgM, Nat.lt_succ_of_le hgtH⟩
    · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, Int.gcd_dvd_left (qOf ω p.1) (qOf ω p.2)⟩,
             ⟨Finset.mem_univ _, Int.gcd_dvd_right (qOf ω p.1) (qOf ω p.2)⟩⟩
  have hA3card1 : (A3.card : ℝ) ≤ ∑ d ∈ Finset.Ioo M (t*H+1), ((C d).card : ℝ)^2 := by
    have h1 : A3.card ≤ ((Finset.Ioo M (t*H+1)).biUnion (fun d => C d ×ˢ C d)).card :=
      Finset.card_le_card hA3sub
    have h2 : ((Finset.Ioo M (t*H+1)).biUnion (fun d => C d ×ˢ C d)).card
        ≤ ∑ d ∈ Finset.Ioo M (t*H+1), (C d ×ˢ C d).card := Finset.card_biUnion_le
    calc (A3.card : ℝ) ≤ ((∑ d ∈ Finset.Ioo M (t*H+1), (C d ×ˢ C d).card : ℕ) : ℝ) := by
          exact_mod_cast le_trans h1 h2
      _ = ∑ d ∈ Finset.Ioo M (t*H+1), (((C d ×ˢ C d).card : ℕ) : ℝ) := by push_cast; rfl
      _ = ∑ d ∈ Finset.Ioo M (t*H+1), ((C d).card : ℝ)^2 := by
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.card_product, pow_two]
          push_cast
          ring
  have hA3card2 : (A3.card : ℝ)
      ≤ ∑ d ∈ Finset.Ioo M (t*H+1), ((1/(d:ℝ) + 1/(H:ℝ)) * K)^2 := by
    refine le_trans hA3card1 (Finset.sum_le_sum fun d hd => ?_)
    have hd1 : 1 ≤ d := by
      have := (Finset.mem_Ioo.mp hd).1
      omega
    have hdvd := hDvd d hd1
    have h0 : 0 ≤ ((C d).card : ℝ) := by positivity
    exact pow_le_pow_left₀ h0 hdvd 2
  -- the arithmetic for the sum
  set AA : ℝ := ∑ d ∈ Finset.Ioo M (t*H+1), ((d:ℝ)^2)⁻¹
  set nD : ℝ := ((Finset.Ioo M (t*H+1)).card : ℝ)
  have hAA : AA ≤ 2 / ((M:ℝ) + 1) := sum_Ioo_inv_sq_le M (t*H+1)
  have hnD : nD ≤ (t:ℝ)*(H:ℝ) + 1 := by
    have h1 : (Finset.Ioo M (t*H+1)).card ≤ t*H + 1 := by
      calc (Finset.Ioo M (t*H+1)).card ≤ (Finset.range (t*H+1)).card :=
            Finset.card_le_card (fun x hx => Finset.mem_range.mpr (Finset.mem_Ioo.mp hx).2)
        _ = t*H + 1 := Finset.card_range _
    calc nD = (((Finset.Ioo M (t*H+1)).card : ℕ) : ℝ) := rfl
      _ ≤ ((t*H+1 : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (t:ℝ)*(H:ℝ) + 1 := by push_cast; ring
  have hsum1 : ∑ d ∈ Finset.Ioo M (t*H+1), ((1/(d:ℝ) + 1/(H:ℝ)) * K)^2
      = K^2 * ∑ d ∈ Finset.Ioo M (t*H+1), (1/(d:ℝ) + 1/(H:ℝ))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hsum2 : ∑ d ∈ Finset.Ioo M (t*H+1), (1/(d:ℝ) + 1/(H:ℝ))^2 ≤ 2*AA + 2*nD*((H:ℝ)^2)⁻¹ := by
    have hpt : ∀ d : ℕ, (1/(d:ℝ) + 1/(H:ℝ))^2
        ≤ 2 * (((d:ℝ)^2)⁻¹) + 2 * (((H:ℝ)^2)⁻¹) := by
      intro d
      have h1 : (1/(d:ℝ) + 1/(H:ℝ))^2 ≤ 2 * (1/(d:ℝ))^2 + 2 * (1/(H:ℝ))^2 := by
        nlinarith [sq_nonneg (1/(d:ℝ) - 1/(H:ℝ))]
      have h2 : (1/(d:ℝ))^2 = ((d:ℝ)^2)⁻¹ := by rw [one_div, inv_pow]
      have h3 : (1/(H:ℝ))^2 = ((H:ℝ)^2)⁻¹ := by rw [one_div, inv_pow]
      rw [h2, h3] at h1
      exact h1
    calc ∑ d ∈ Finset.Ioo M (t*H+1), (1/(d:ℝ) + 1/(H:ℝ))^2
        ≤ ∑ d ∈ Finset.Ioo M (t*H+1), (2 * (((d:ℝ)^2)⁻¹) + 2 * (((H:ℝ)^2)⁻¹)) :=
          Finset.sum_le_sum fun d _ => hpt d
      _ = 2*AA + 2*nD*((H:ℝ)^2)⁻¹ := by
          rw [Finset.sum_add_distrib]
          have e1 : (∑ d ∈ Finset.Ioo M (t*H+1), 2 * (((d:ℝ)^2)⁻¹)) = 2 * AA := by
            show (∑ d ∈ Finset.Ioo M (t*H+1), 2 * (((d:ℝ)^2)⁻¹))
              = 2 * (∑ d ∈ Finset.Ioo M (t*H+1), (((d:ℝ)^2)⁻¹))
            rw [Finset.mul_sum]
          have e2 : (∑ _x ∈ Finset.Ioo M (t*H+1), 2 * (((H:ℝ)^2)⁻¹))
              = 2 * nD * ((H:ℝ)^2)⁻¹ := by
            show (∑ _x ∈ Finset.Ioo M (t*H+1), 2 * (((H:ℝ)^2)⁻¹))
              = 2 * ((Finset.Ioo M (t*H+1)).card : ℝ) * ((H:ℝ)^2)⁻¹
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
          rw [e1, e2]
  have hHg : 2*nD*((H:ℝ)^2)⁻¹ ≤ (2*(t:ℝ)+2)/(H:ℝ) := by
    have hHne : (H:ℝ) ≠ 0 := by positivity
    have hnD1 : 2*nD*((H:ℝ)^2)⁻¹ ≤ 2*((t:ℝ)*(H:ℝ)+1)*((H:ℝ)^2)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [hnD]
    have hkey : 2*((t:ℝ)*(H:ℝ)+1) ≤ (2*(t:ℝ)+2)*(H:ℝ) := by
      have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
      nlinarith [hH1]
    have h2 : 2*((t:ℝ)*(H:ℝ)+1)*((H:ℝ)^2)⁻¹ ≤ (2*(t:ℝ)+2)/(H:ℝ) := by
      calc 2*((t:ℝ)*(H:ℝ)+1)*((H:ℝ)^2)⁻¹
          ≤ ((2*(t:ℝ)+2)*(H:ℝ))*((H:ℝ)^2)⁻¹ :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = (2*(t:ℝ)+2)/(H:ℝ) := by
            field_simp
    linarith [hnD1, h2]
  have hMgcd : (A3.card : ℝ) ≤ K^2 * (4*η + (2*(t:ℝ)+2)/(H:ℝ)) := by
    have step1 : (A3.card : ℝ) ≤ K^2 * (2*AA + 2*nD*((H:ℝ)^2)⁻¹) := by
      calc (A3.card : ℝ) ≤ ∑ d ∈ Finset.Ioo M (t*H+1), ((1/(d:ℝ) + 1/(H:ℝ)) * K)^2 := hA3card2
        _ = K^2 * ∑ d ∈ Finset.Ioo M (t*H+1), (1/(d:ℝ) + 1/(H:ℝ))^2 := hsum1
        _ ≤ K^2 * (2*AA + 2*nD*((H:ℝ)^2)⁻¹) :=
            mul_le_mul_of_nonneg_left hsum2 (by positivity)
    have h4 : 4 / ((M:ℝ) + 1) ≤ 4*η := by
      have hηM : 1 < η * ((M:ℝ) + 1) := by
        have := (div_lt_iff₀ hη0).mp hMlt
        linarith [this]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < (M:ℝ) + 1)]
      nlinarith [hηM]
    have step2 : 2*AA + 2*nD*((H:ℝ)^2)⁻¹ ≤ 4*η + (2*(t:ℝ)+2)/(H:ℝ) := by
      have h1 : 2*AA ≤ 4/((M:ℝ)+1) := by
        have h3 : 4/((M:ℝ)+1) = 2 * (2/((M:ℝ)+1)) := by ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left hAA (by norm_num)
      exact add_le_add (le_trans h1 h4) hHg
    calc (A3.card : ℝ) ≤ K^2 * (2*AA + 2*nD*((H:ℝ)^2)⁻¹) := step1
      _ ≤ K^2 * (4*η + (2*(t:ℝ)+2)/(H:ℝ)) :=
          mul_le_mul_of_nonneg_left step2 (by positivity)
  -- (e) finish
  have htotal : (S.card : ℝ) ≤ K^2 * (8*η + (2*(t:ℝ)+4)/(H:ℝ)) := by
    have h1 : (2*η + 1/(H:ℝ)) * K * K = (2*η + 1/(H:ℝ)) * K^2 := by ring
    have hA1 := hA1card; rw [h1] at hA1
    have hA2 := hA2card; rw [h1] at hA2
    have hfin : K^2 * (8*η + (2*(t:ℝ)+4)/(H:ℝ))
        = ((2*η + 1/(H:ℝ)) * K^2 + (2*η + 1/(H:ℝ)) * K^2)
          + K^2 * (4*η + (2*(t:ℝ)+2)/(H:ℝ)) := by ring
    rw [hfin]
    exact le_trans hcard (add_le_add (add_le_add hA1 hA2) hMgcd)
  have hfinal : K^2 * (8*η + (2*(t:ℝ)+4)/(H:ℝ))
      ≤ (8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) * K^2 := by
    have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
    have hK2 : 0 ≤ K^2 := sq_nonneg K
    have hmain : 8*η + (2*(t:ℝ)+4)/(H:ℝ) ≤ (8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) := by
      have h1 : (2*(t:ℝ)+4)/(H:ℝ) ≤ (8+2*(t:ℝ))/(H:ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith only [ht]
      have h2 : 8*η ≤ (8+2*(t:ℝ))*η := by nlinarith only [ht, hη0']
      have h3 : (8+2*(t:ℝ))/(H:ℝ) = (8+2*(t:ℝ))*(1/(H:ℝ)) := by rw [div_eq_mul_inv, one_div]
      rw [h3] at h1
      have h4 : (8 + 2*(t:ℝ)) * (η + 1/(H:ℝ))
          = (8+2*(t:ℝ))*η + (8+2*(t:ℝ))*(1/(H:ℝ)) := by ring
      rw [h4]
      exact add_le_add h2 h1
    calc K^2 * (8*η + (2*(t:ℝ)+4)/(H:ℝ))
        ≤ K^2 * ((8 + 2*(t:ℝ)) * (η + 1/(H:ℝ))) := mul_le_mul_of_nonneg_left hmain hK2
      _ = (8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) * K^2 := by ring
  linarith only [htotal, hfinal]

open Classical in
/-- **(GEN) Genericity count** for the slopes `ω·(h−h')` of the regime swap: the number of `ι` with some slot `k` failing `genPair H η` is at most `C_t(η + 1/H)·#ι`. -/
theorem genericCount : ∀ t : ℕ, 1 ≤ t → ∃ C : ℝ, 0 < C ∧
    ∀ (H : ℕ) (η : ℝ), 1 ≤ H → 0 < η → η ≤ 1 →
      ((Finset.univ.filter (fun ι : (Fin (2 ^ t - 1) → Bool) →
            ((Fin t → Fin H) × (Fin t → Fin H)) =>
          ∃ k : Fin (Work.Peluse.LadderP.Swap.slotCard (2 ^ t - 1)),
            ¬ Work.Peluse.LadderP.Swap.genPair H η
              (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf t
                  (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).1)
                (Work.Peluse.Concat.tupSub (ι (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).2.1).1
                  (ι (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).2.1).2))
              (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf t
                  (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).1)
                (Work.Peluse.Concat.tupSub (ι (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).2.2).1
                  (ι (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).2.2).2)))).card : ℝ)
        ≤ C * (η + 1 / (H : ℝ)) *
          (Fintype.card ((Fin (2 ^ t - 1) → Bool) →
            ((Fin t → Fin H) × (Fin t → Fin H))) : ℝ) := by
  intro t ht
  refine ⟨1 + (LadderP.Swap.slotCard (2 ^ t - 1) : ℝ) * (16 * ((t:ℝ) + 1)), ?_, ?_⟩
  · -- positivity of the constant
    have h1 : (0:ℝ) ≤ (LadderP.Swap.slotCard (2 ^ t - 1) : ℝ) := by positivity
    have h2 : (0:ℝ) ≤ 16 * ((t:ℝ) + 1) := by positivity
    linarith [mul_nonneg h1 h2]
  intro H η hH hη0 hη1
  haveI hplugne : Nonempty (Plug t H) :=
    ⟨(fun _ => ⟨0, (show 0 < H by omega)⟩, fun _ => ⟨0, (show 0 < H by omega)⟩)⟩
  have hNpos : (0:ℝ) < (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) := by
    have h := Fintype.card_pos (α := (Fin (2^t-1) → Bool) → Plug t H)
    exact_mod_cast h
  have hKpos : (0:ℝ) < (Fintype.card (Plug t H) : ℝ) := by
    have h := Fintype.card_pos (α := Plug t H)
    exact_mod_cast h
  have hK2pos : (0:ℝ) < (Fintype.card (Plug t H) : ℝ)^2 := by positivity
  -- ## Per-slot bound
  have hBk : ∀ k : Fin (LadderP.Swap.slotCard (2^t-1)),
      ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H => slotBad η k ι)).card : ℝ)
        ≤ (8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) *
          (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) := by
    intro k
    have hωk : Holds.omegaOf t (LadderP.Swap.slotAt (2^t-1) k).1 ≠ 0 :=
      Holds.omegaOf_ne_zero t _
    have hfib := evalPairFiber (V := Plug t H) (slotAt_ne (2 ^ t - 1) k)
      (badPairs (t := t) (H := H) (Holds.omegaOf t (LadderP.Swap.slotAt (2^t-1) k).1) η)
    have hfilt : (Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H => slotBad η k ι))
        = Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
            (ι (LadderP.Swap.slotAt (2^t-1) k).2.1, ι (LadderP.Swap.slotAt (2^t-1) k).2.2)
              ∈ badPairs (t := t) (H := H) (Holds.omegaOf t (LadderP.Swap.slotAt (2^t-1) k).1) η) := by
      apply Finset.filter_congr
      intro ι _
      exact slotBad_iff
    have hbp := card_badPairs ht hH (Holds.omegaOf t (LadderP.Swap.slotAt (2^t-1) k).1) hωk hη0 hη1
    have key : ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
            slotBad η k ι)).card : ℝ) * (Fintype.card (Plug t H) : ℝ)^2
        = ((badPairs (t := t) (H := H) (Holds.omegaOf t (LadderP.Swap.slotAt (2^t-1) k).1) η).card : ℝ)
          * (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) := by
      rw [hfilt]; exact hfib
    have h2 : ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
            slotBad η k ι)).card : ℝ) * (Fintype.card (Plug t H) : ℝ)^2
        ≤ ((8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) *
            (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ)) * (Fintype.card (Plug t H) : ℝ)^2 := by
      rw [key]
      calc ((badPairs (t := t) (H := H) (Holds.omegaOf t (LadderP.Swap.slotAt (2^t-1) k).1) η).card : ℝ)
              * (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ)
          ≤ ((8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) * (Fintype.card (Plug t H) : ℝ)^2)
              * (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) :=
            mul_le_mul_of_nonneg_right hbp (le_of_lt hNpos)
        _ = ((8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) *
              (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ)) * (Fintype.card (Plug t H) : ℝ)^2 := by
            ring
    exact (mul_le_mul_iff_of_pos_right hK2pos).mp h2
  -- ## Union over slots
  have hsub : (Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
        ∃ k, slotBad η k ι))
      ⊆ (Finset.univ : Finset (Fin (LadderP.Swap.slotCard (2^t-1)))).biUnion
          (fun k => Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H => slotBad η k ι)) := by
    intro ι hι
    rw [Finset.mem_filter] at hι
    obtain ⟨-, k, hk⟩ := hι
    rw [Finset.mem_biUnion]
    exact ⟨k, Finset.mem_univ _, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hk⟩⟩
  have hmain : ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
          ∃ k, slotBad η k ι)).card : ℝ)
      ≤ (1 + (LadderP.Swap.slotCard (2^t-1) : ℝ) * (16 * ((t:ℝ) + 1))) * (η + 1/(H:ℝ)) *
          (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) := by
    have hcard : ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
          ∃ k, slotBad η k ι)).card : ℝ)
        ≤ ∑ k : Fin (LadderP.Swap.slotCard (2^t-1)),
            (8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) *
              (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) := by
      have h1 : (Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
            ∃ k, slotBad η k ι)).card
          ≤ ∑ k : Fin (LadderP.Swap.slotCard (2^t-1)),
              (Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
                slotBad η k ι)).card :=
        le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
      calc ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
              ∃ k, slotBad η k ι)).card : ℝ)
          ≤ ((∑ k : Fin (LadderP.Swap.slotCard (2^t-1)),
              (Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
                slotBad η k ι)).card : ℕ) : ℝ) := by exact_mod_cast h1
        _ = ∑ k : Fin (LadderP.Swap.slotCard (2^t-1)),
              ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
                slotBad η k ι)).card : ℝ) := by push_cast; rfl
        _ ≤ ∑ k : Fin (LadderP.Swap.slotCard (2^t-1)),
              (8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) *
                (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) :=
            Finset.sum_le_sum fun k _ => hBk k
    have hsum : ∑ k : Fin (LadderP.Swap.slotCard (2^t-1)),
          (8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) *
            (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ)
        = (LadderP.Swap.slotCard (2^t-1) : ℝ) *
          ((8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) *
            (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    have hstep := le_trans hcard (le_of_eq hsum)
    have hC : (8 + 2*(t:ℝ)) ≤ 16 * ((t:ℝ) + 1) := by linarith only [ht]
    have hslot0 : (0:ℝ) ≤ (LadderP.Swap.slotCard (2^t-1) : ℝ) := by positivity
    have hcoef0 : (0:ℝ) ≤ η + 1/(H:ℝ) := by
      have hHp : (0:ℝ) < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
      have h3 : (0:ℝ) < 1/(H:ℝ) := by positivity
      linarith [hη0.le, h3]
    have hN0 : (0:ℝ) ≤ (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) := le_of_lt hNpos
    have hstep2 : ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
            ∃ k, slotBad η k ι)).card : ℝ)
        ≤ (LadderP.Swap.slotCard (2^t-1) : ℝ) *
            ((16 * ((t:ℝ) + 1)) * (η + 1/(H:ℝ)) *
              (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ)) := by
      calc ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
              ∃ k, slotBad η k ι)).card : ℝ)
          ≤ (LadderP.Swap.slotCard (2^t-1) : ℝ) *
              ((8 + 2*(t:ℝ)) * (η + 1/(H:ℝ)) *
                (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ)) := hstep
        _ ≤ (LadderP.Swap.slotCard (2^t-1) : ℝ) *
              ((16 * ((t:ℝ) + 1)) * (η + 1/(H:ℝ)) *
                (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hslot0
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hcoef0) hN0
    have hstep3 : (LadderP.Swap.slotCard (2^t-1) : ℝ) *
            ((16 * ((t:ℝ) + 1)) * (η + 1/(H:ℝ)) *
              (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ))
        = ((LadderP.Swap.slotCard (2^t-1) : ℝ) * (16 * ((t:ℝ) + 1))) * (η + 1/(H:ℝ)) *
            (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) := by ring
    rw [hstep3] at hstep2
    have hX : (LadderP.Swap.slotCard (2^t-1) : ℝ) * (16 * ((t:ℝ) + 1))
        ≤ 1 + (LadderP.Swap.slotCard (2^t-1) : ℝ) * (16 * ((t:ℝ) + 1)) := by linarith
    calc ((Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
            ∃ k, slotBad η k ι)).card : ℝ)
        ≤ ((LadderP.Swap.slotCard (2^t-1) : ℝ) * (16 * ((t:ℝ) + 1))) * (η + 1/(H:ℝ)) *
            (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) := hstep2
      _ ≤ (1 + (LadderP.Swap.slotCard (2^t-1) : ℝ) * (16 * ((t:ℝ) + 1))) * (η + 1/(H:ℝ)) *
            (Fintype.card ((Fin (2^t-1) → Bool) → Plug t H) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX hcoef0) hN0
  -- ## Bridge to the statement of `genericCount`
  have hgoal : (Finset.univ.filter (fun ι : (Fin (2^t-1) → Bool) → Plug t H =>
        ∃ k, slotBad η k ι))
      = (Finset.univ.filter (fun ι : (Fin (2 ^ t - 1) → Bool) →
            ((Fin t → Fin H) × (Fin t → Fin H)) =>
          ∃ k : Fin (Work.Peluse.LadderP.Swap.slotCard (2 ^ t - 1)),
            ¬ Work.Peluse.LadderP.Swap.genPair H η
              (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf t
                  (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).1)
                (Work.Peluse.Concat.tupSub (ι (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).2.1).1
                  (ι (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).2.1).2))
              (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf t
                  (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).1)
                (Work.Peluse.Concat.tupSub (ι (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).2.2).1
                  (ι (Work.Peluse.LadderP.Swap.slotAt (2 ^ t - 1) k).2.2).2)))) := by
    apply Finset.filter_congr
    intro ι _
    simp only [slotBad, qOf]
  rw [← hgoal]
  exact hmain

end

end Work.Peluse.SwapA
