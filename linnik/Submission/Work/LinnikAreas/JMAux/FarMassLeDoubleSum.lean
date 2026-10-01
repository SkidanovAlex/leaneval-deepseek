import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery

namespace Work.LinnikAreas.JMAux

open scoped Classical BigOperators
open DirichletCharacter Complex
open Work.LinnikContract Work.LinnikAreas

/-- If `(χ,ρ)` is a non-principal zero with nonzero multiplicity, `L ≥ log q`, and the box
condition `InBox q R ρ` fails, then `R < max((1 - Re ρ)·L) (|Im ρ|·L)`.  This is the only place
where the hypothesis `log q ≤ L` is used in the reduction; it lets us replace `log q` by `L`. -/
lemma lt_max_of_not_InBox {q : ℕ} [NeZero q] {L R : ℝ} (hLq : Real.log (q:ℝ) ≤ L)
    {z : DirichletCharacter ℂ q × ℂ} (hz1 : z.1 ≠ 1) (hz0 : zeroMult z.1 z.2 ≠ 0)
    (hz2 : ¬ InBox q R z.2) :
    R < max ((1 - z.2.re) * L) (|z.2.im| * L) := by
  by_contra hc
  push_neg at hc
  have hre : 0 ≤ 1 - z.2.re := by have h := (zeroMult_re z.1 hz1 hz0).2; linarith
  refine hz2 ⟨?_, ?_⟩
  · rw [lamOf]
    calc (1 - z.2.re) * Real.log (q:ℝ) ≤ (1 - z.2.re) * L :=
          mul_le_mul_of_nonneg_left hLq hre
      _ ≤ R := le_trans (le_max_left _ _) hc
  · calc |z.2.im| * Real.log (q:ℝ) ≤ |z.2.im| * L :=
          mul_le_mul_of_nonneg_left hLq (abs_nonneg _)
      _ ≤ R := le_trans (le_max_right _ _) hc

lemma FarMassLeDoubleSum {q : ℕ} [NeZero q] (R : ℕ) (hR : 1 ≤ R) {L : ℝ} (hL : 0 < L)
    (hLq : Real.log (q:ℝ) ≤ L)
    (K : ℕ) (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hK : ∀ z ∈ S, z.1 ≠ 1 → ¬ Work.LinnikContract.InBox q (R:ℝ) z.2 →
      Work.LinnikContract.zeroMult z.1 z.2 ≠ 0 →
      max (Work.LinnikAreas.farM L z : ℝ) (Work.LinnikAreas.farY L z) + 1 ≤ (2:ℝ)^K) :
    Work.LinnikAreas.farMassSum R L S
      ≤ 32 * ∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
          * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
              * Work.LinnikAreas.cellMult L (Work.LinnikAreas.farPairs R S) m k := by
  classical
  have hLpos : 0 < L := hL
  set S₁ : Finset (DirichletCharacter ℂ q × ℂ) := farPairs R S with hS1
  have hS1mem : ∀ z ∈ S₁, z ∈ S ∧ z.1 ≠ 1 ∧ ¬ InBox q (R:ℝ) z.2
      ∧ zeroMult z.1 z.2 ≠ 0 := by
    intro z hz
    rw [hS1, farPairs, Finset.mem_filter, Finset.mem_filter] at hz
    exact ⟨hz.1.1, hz.1.2.1, hz.1.2.2, hz.2⟩
  -- step 1: reduce to the far, non-principal, nonzero-multiplicity pairs
  have hstep1 : farMassSum R L S
      = ∑ z ∈ S₁, (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖ := by
    rw [farMassSum]
    have hS1sub : S₁ ⊆ S := fun z hz => (hS1mem z hz).1
    have hzero : ∀ z ∈ S, z ∉ S₁ →
        (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
          else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖) = 0 := by
      intro z hz hnot
      by_cases h1 : z.1 = 1
      · simp [h1]
      · have h3 : InBox q (R:ℝ) z.2 ∨ zeroMult z.1 z.2 = 0 := by
          by_contra hc
          push_neg at hc
          exact hnot (by
            rw [hS1, farPairs, Finset.mem_filter, Finset.mem_filter]
            exact ⟨⟨hz, h1, hc.1⟩, hc.2⟩)
        rcases h3 with h3 | h3
        · simp [h1, h3]
        · simp [h1, h3]
    have hcong : ∀ z ∈ S₁,
        (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
          else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖)
        = (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖ := by
      intro z hz
      obtain ⟨-, hz1, hz2, -⟩ := hS1mem z hz
      simp only [if_neg hz1, if_neg hz2]
    rw [← Finset.sum_subset hS1sub hzero]
    exact Finset.sum_congr rfl hcong
  -- the layer bound `K` for the pairs in `S₁`, from the hypothesis
  have hK' : ∀ z ∈ S₁, max (farM L z : ℝ) (farY L z) + 1 ≤ (2:ℝ)^K := by
    intro z hz
    obtain ⟨hzS, hz1, hz2, hz0⟩ := hS1mem z hz
    exact hK z hzS hz1 hz2 hz0
  -- pointwise weight bound
  have hweight : ∀ z ∈ S₁, (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖
      ≤ 32 * (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))
          * farLayer K R (farM L z) (farY L z) := by
    intro z hz
    obtain ⟨-, hz1, hz2, hz0⟩ := hS1mem z hz
    have hfar : (R:ℝ) < max ((1 - z.2.re) * L) (|z.2.im| * L) :=
      lt_max_of_not_InBox hLq hz1 hz0 hz2
    have h1 := Hk_le_farLayer R hR hLpos hz1 hz0 hfar K (hK' z hz)
    calc (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖
        ≤ (zeroMult z.1 z.2 : ℝ) * (32 * Real.exp (-(49/10) * (farM L z : ℝ))
            * farLayer K R (farM L z) (farY L z)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = 32 * (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))
            * farLayer K R (farM L z) (farY L z) := by ring
  -- step 2: sum the pointwise bounds
  have hstep2 : (∑ z ∈ S₁, (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖)
      ≤ 32 * ∑ m ∈ Finset.range (Nat.ceil L + 1),
          Real.exp (-(49/10) * (m:ℝ))
          * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k
              * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
              * cellMult L S₁ m k := by
    refine le_trans (Finset.sum_le_sum hweight) ?_
    have hexp : (∑ z ∈ S₁, 32 * (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))
          * farLayer K R (farM L z) (farY L z))
        = 32 * ∑ z ∈ S₁, ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (farM L z : ℝ) ≤ (2:ℝ)^k
                then (1:ℝ) else 0)
            * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [farLayer, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [hexp]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 32)
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := S₁) (t := Finset.range (Nat.ceil L + 1)) (g := fun z => farM L z)
      (f := fun z => ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k
        * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (farM L z : ℝ) ≤ (2:ℝ)^k
            then (1:ℝ) else 0)
        * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))))
      (fun z hz => by
        have h := zeroMult_re z.1 (hS1mem z hz).2.1 (hS1mem z hz).2.2.2
        have hX0 : 0 ≤ (1 - z.2.re) * L := by nlinarith [h.2]
        rw [Finset.mem_range]
        have hlt : (farM L z : ℝ) < L := by
          have h2 : (farM L z : ℝ) ≤ (1 - z.2.re) * L := Nat.floor_le hX0
          nlinarith [h.1]
        have : ((farM L z : ℕ) : ℝ) < ((Nat.ceil L + 1 : ℕ) : ℝ) := by
          push_cast
          linarith [Nat.le_ceil L]
        exact_mod_cast this)
    rw [← hfib]
    refine Finset.sum_le_sum (fun m _ => ?_)
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun k _ => ?_)
    -- the conditional involving `farY` becomes a filter, and `farM z = m` on the cell
    have h1 : (∑ z ∈ S₁.filter (fun z => farM L z = m), (1/4:ℝ)^k
          * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (farM L z : ℝ) ≤ (2:ℝ)^k
              then (1:ℝ) else 0)
          * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))))
        = ∑ z ∈ S₁.filter (fun z => farM L z = m),
            (if farY L z ≤ (2:ℝ)^k
              then (1/4:ℝ)^k * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
                * (Real.exp (-(49/10) * (m:ℝ)) * (zeroMult z.1 z.2 : ℝ))
              else 0) := by
      refine Finset.sum_congr rfl (fun z hz => ?_)
      have hzm : farM L z = m := (Finset.mem_filter.mp hz).2
      rw [hzm]
      by_cases h : farY L z ≤ (2:ℝ)^k
      · by_cases hc : (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k
        · rw [if_pos h]
          rw [if_pos ⟨hc.1, h, hc.2⟩]
          rw [if_pos hc]
          ring
        · rw [if_pos h]
          rw [if_neg (fun hcc : (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k
            => hc ⟨hcc.1, hcc.2.2⟩)]
          rw [if_neg hc]
          ring
      · rw [if_neg h]
        rw [if_neg (fun hcc : (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k
          => h hcc.2.1)]
        ring
    rw [h1, ← Finset.sum_filter]
    rw [cellMult]
    rw [show (∑ z ∈ S₁.filter (fun z => farM L z = m ∧ farY L z ≤ (2:ℝ)^k),
              (zeroMult z.1 z.2 : ℝ))
          = ∑ z ∈ (S₁.filter (fun z => farM L z = m)).filter (fun z => farY L z ≤ (2:ℝ)^k),
              (zeroMult z.1 z.2 : ℝ) from
        Finset.sum_congr (Finset.filter_filter (fun z => farM L z = m)
          (fun z => farY L z ≤ (2:ℝ)^k) S₁).symm (fun _ _ => rfl)]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun z _ => le_of_eq (by ring))
  exact le_trans hstep1.le hstep2

end Work.LinnikAreas.JMAux
