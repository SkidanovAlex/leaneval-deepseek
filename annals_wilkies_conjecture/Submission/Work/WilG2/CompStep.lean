/-
  WilG2 : from the `OrderedFinpartition` Faa di Bruno bound to the `Composition` bound,
  and the final assembly of `G2_tnorm_comp`.

  The two combinatorics inputs are stated as explicit hypotheses here:
  * `hcount` : `Work.WilG2.ofp_weighted_sum`  (weighted counting identity)
  * `hsum`   : `Work.WilG2.sum_composition_mul_prod_le` (composition-sum domination)
-/
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG2.Tnorm
import Submission.Work.WilG2.CompBound

set_option autoImplicit false
noncomputable section
open Classical Finset
namespace WilkiesDesign.CG
open WilkiesConjecture WilkiesDesign FirstOrder Language

/-- Reindexing `Ico 1 (r+1)` as `Fin r` (via `j ↦ j + 1`). -/
theorem sum_Ico_one_eq_sum_fin (r : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ Finset.Ico 1 (r + 1), a j) = ∑ j : Fin r, a (j + 1) := by
  rw [Finset.sum_Ico_eq_sum_range (fun k => a k) 1 (r + 1), Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun j => a (j + 1)) r]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]

/-- The multinomial expansion of a power of a finite sum of `r` terms. -/
theorem sum_pi_fin_pow (r p : ℕ) (a : ℕ → ℝ) :
    (∑ j : Fin r, a (j + 1)) ^ p = ∑ f : Fin p → Fin r, ∏ i : Fin p, a (f i + 1) := by
  rw [Fintype.sum_pow]

/-- **The composition bound for one order.**  Given the weighted counting identity
(stating that the `OrderedFinpartition` Faa di Bruno sum, weighted by `c.length! * ∏ partSize!`,
equals `n!` times the `Composition` sum), the `n`-th Taylor coefficient of `g ∘ F` is bounded by
the corresponding `Composition` sum of Taylor coefficients. -/
theorem jetCoeff_comp_le_of_counting {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (r n : ℕ) (hn : n ≤ r) (F : E → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (x : E)
    (hF : ContDiffAt ℝ r F x) (hg : ContDiffAt ℝ r g (F x))
    (hcount : (∑ c : OrderedFinpartition n,
        ((c.length.factorial : ℝ) * ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)) *
          (jetCoeff c.length g (F x) * ∏ i : Fin c.length, jetCoeff (c.partSize i) F x))
      = (n.factorial : ℝ) * ∑ c : Composition n,
          jetCoeff c.length g (F x) * ∏ i : Fin c.length, jetCoeff (c.blocksFun i) F x) :
    jetCoeff n (g ∘ F) x ≤
      ∑ c : Composition n,
        jetCoeff c.length g (F x) * ∏ i : Fin c.length, jetCoeff (c.blocksFun i) F x := by
  have hb := norm_iteratedFDeriv_comp_le_ofp r n hn F g x hF hg
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hsub : (∑ c : OrderedFinpartition n, ‖iteratedFDeriv ℝ c.length g (F x)‖ *
        ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) F x‖)
      = ∑ c : OrderedFinpartition n,
        ((c.length.factorial : ℝ) * ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)) *
          (jetCoeff c.length g (F x) * ∏ i : Fin c.length, jetCoeff (c.partSize i) F x) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : ‖iteratedFDeriv ℝ c.length g (F x)‖ =
        (c.length.factorial : ℝ) * jetCoeff c.length g (F x) := by
      have hk : ((c.length.factorial : ℝ)) ≠ 0 := by exact_mod_cast c.length.factorial_ne_zero
      rw [jetCoeff, mul_comm, div_mul_cancel₀ _ hk]
    have h2 : (∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) F x‖)
        = ∏ i : Fin c.length,
            (((c.partSize i).factorial : ℝ) * jetCoeff (c.partSize i) F x) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      have hk : (((c.partSize i).factorial : ℝ)) ≠ 0 := by
        exact_mod_cast (c.partSize i).factorial_ne_zero
      rw [jetCoeff, mul_comm, div_mul_cancel₀ _ hk]
    rw [h1, h2, Finset.prod_mul_distrib]
    ring
  rw [hsub, hcount] at hb
  rw [jetCoeff, div_le_iff₀ hfac]
  exact hb.trans_eq (mul_comm _ _)

/-- **`G2_tnorm_comp`**, from the two combinatorics inputs. -/
theorem G2_tnorm_comp_of_inputs {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (r : ℕ) (F : E → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (x : E)
    (hF : ContDiffAt ℝ r F x) (hg : ContDiffAt ℝ r g (F x))
    (h1 : ∑ k ∈ Finset.Ico 1 (r + 1), ‖iteratedFDeriv ℝ k F x‖ / (k.factorial : ℝ) ≤ 1)
    (hcounting : ∀ n ≤ r,
      (∑ c : OrderedFinpartition n,
        ((c.length.factorial : ℝ) * ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)) *
          (jetCoeff c.length g (F x) * ∏ i : Fin c.length, jetCoeff (c.partSize i) F x))
      = (n.factorial : ℝ) * ∑ c : Composition n,
          jetCoeff c.length g (F x) * ∏ i : Fin c.length, jetCoeff (c.blocksFun i) F x)
    (hcomp : (∑ n ∈ Finset.range (r + 1),
        ∑ c : Composition n,
          jetCoeff c.length g (F x) * ∏ i : Fin c.length, jetCoeff (c.blocksFun i) F x)
      ≤ ∑ p ∈ Finset.range (r + 1),
          jetCoeff p g (F x) * (∑ j : Fin r, jetCoeff (j + 1) F x) ^ p) :
    tnorm r (g ∘ F) x ≤ tnorm r g (F x) := by
  rw [tnorm_eq_sum_jetCoeff, tnorm_eq_sum_jetCoeff]
  have hbase : (∑ j : Fin r, jetCoeff (j + 1) F x) ≤ 1 := by
    rw [← sum_Ico_one_eq_sum_fin r (fun k => jetCoeff k F x)]
    simpa only [jetCoeff] using h1
  have hle1 : ∀ p : ℕ, (∑ j : Fin r, jetCoeff (j + 1) F x) ^ p ≤ 1 :=
    fun p => pow_le_one₀ (Finset.sum_nonneg fun j _ => jetCoeff_nonneg (j + 1) F x) hbase
  calc (∑ n ∈ Finset.range (r + 1), jetCoeff n (g ∘ F) x)
      ≤ ∑ n ∈ Finset.range (r + 1), ∑ c : Composition n,
          jetCoeff c.length g (F x) * ∏ i : Fin c.length, jetCoeff (c.blocksFun i) F x :=
        Finset.sum_le_sum fun n hn =>
          jetCoeff_comp_le_of_counting r n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
            F g x hF hg (hcounting n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))
    _ ≤ ∑ p ∈ Finset.range (r + 1),
          jetCoeff p g (F x) * (∑ j : Fin r, jetCoeff (j + 1) F x) ^ p := hcomp
    _ ≤ ∑ p ∈ Finset.range (r + 1), jetCoeff p g (F x) :=
        Finset.sum_le_sum fun p _ =>
          mul_le_of_le_one_right (jetCoeff_nonneg p g (F x)) (hle1 p)

end WilkiesDesign.CG
