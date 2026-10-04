/-
# `Work.Diff.STE.flat.level_linear`-companion: the `pairing_bound` estimate

This file assembles the static (one-time) bound on the level-`(s+1)` energy pairing
`Σ_{i,j} [ Σ_l L2re (∂^l (Φ ∘ jet)) (∂^l u_{ij}) + L2re (Φ ∘ jet) u_{ij} ]`

used by the multi-level a priori estimate `Work.Diff.STE.flat.level_step`.

The ingredients are:

* `Work.Diff.STE.flat.Phi_decomp_smooth` — the pointwise decomposition
  `Φ (x, jetM u x) = Σ_{a,b} symInvC c a b x · ∂_a∂_b u + Nfun (x, jetP c x)`;
* `decomp_pairing_le` (this file) — the resulting split of the pairing into the Gårding
  (principal) part, the Leibniz commutator and the lower-order term;
* `Work.Diff.STE.flat.pairing_gard_le` — the Gårding dissipation
  `-(lam'/2) · ENormSqM (s+2) u`;
* `Work.Diff.STE.flat.pairing_rest_le` — the absorption of the commutator and lower-order terms
  into `θ · ENormSqM (s+2) u + C (1 + ENormSqFull (s+1) u)`;
* the elementary zeroth-order bound (this file).
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.commutator_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

noncomputable section

open Work.Diff.STE.Flat

/-! ## Elementary sum manipulations -/

/-- Distributing a double sum of pointwise sums. -/
lemma sum2_add_distrib' {ι κ : Type*} [Fintype ι] [Fintype κ] (F G : ι → κ → ℝ) :
    (∑ a, ∑ b, (F a b + G a b)) = (∑ a, ∑ b, F a b) + (∑ a, ∑ b, G a b) := by
  simp only [Finset.sum_add_distrib]

/-- Cyclic swap of a triple sum. -/
lemma sum3_swap {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (H : ι → κ → τ → ℝ) : (∑ a, ∑ b, ∑ l, H a b l) = ∑ l, ∑ a, ∑ b, H a b l := by
  rw [← Fintype.sum_prod_type (f := fun p : ι × κ => ∑ l, H p.1 p.2 l)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  exact Fintype.sum_prod_type (f := fun p : ι × κ => H p.1 p.2 l)

/-! ## The decomposition of the pairing -/

/-- **The decomposition of the level-`(s+1)` pairing.**  Splits the pairing of the nonlinearity
into the Gårding (principal) part, the Leibniz commutator corrections and the lower-order term. -/
lemma decomp_pairing_le {n s : ℕ} (f : (Fin n → ℝ) → MatC n) (Nf : (Fin n → ℝ) → MatC n)
    (A : Fin n → Fin n → (Fin n → ℝ) → ℂ) (c : (Fin n → ℤ) → MatC n)
    (hdec : ∀ (x : Fin n → ℝ) (i j : Fin n),
      f x i j = (∑ a, ∑ b, A a b x * pd a (pd b (fun z => seriesFunM c z i j)) x) + Nf x i j)
    (hAsm : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b))
    (hNfsm : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => Nf x i j))
    (hSer : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j))
    (i j : Fin n) :
    (∑ l : Fin (s + 1) → Fin n,
        L2re (pdVec (s + 1) l (fun x => f x i j))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
      ≤ (∑ l : Fin (s + 1) → Fin n,
          L2re (fun x => ∑ a, ∑ b, A a b x
              * pd a (pd b (pdVec (s + 1) l (fun x => seriesFunM c x i j))) x)
            (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        + (∑ a, ∑ b, |∑ l : Fin (s + 1) → Fin n,
            L2re (fun x => pdVec (s + 1) l (fun y => A a b y
                  * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                - A a b x * pdVec (s + 1) l
                    (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
              (pdVec (s + 1) l (fun x => seriesFunM c x i j))|)
        + |∑ l : Fin (s + 1) → Fin n,
            L2re (pdVec (s + 1) l (fun x => Nf x i j))
              (pdVec (s + 1) l (fun x => seriesFunM c x i j))| := by
  classical
  have hgab : ∀ a b : Fin n,
      ContDiff ℝ (⊤ : ℕ∞) (fun y => pd a (pd b (fun z => seriesFunM c z i j)) y) :=
    fun a b => contDiff_pd_top (contDiff_pd_top (hSer i j) b) a
  have hf : (fun x : Fin n → ℝ => f x i j)
      = fun x => (∑ a, ∑ b, A a b x * pd a (pd b (fun z => seriesFunM c z i j)) x)
          + Nf x i j := by
    funext x; exact hdec x i j
  have hpd : ∀ l : Fin (s + 1) → Fin n,
      pdVec (s + 1) l (fun x => f x i j)
        = fun x => (∑ a, ∑ b, pdVec (s + 1) l
              (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y) x)
          + pdVec (s + 1) l (fun x => Nf x i j) x := by
    intro l
    rw [hf]
    exact pdVec_sum2_add l (fun a b y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y)
      (fun x => Nf x i j) (fun a b => (hAsm a b).mul (hgab a b)) (hNfsm i j)
  have hl2 : ∀ l : Fin (s + 1) → Fin n,
      L2re (pdVec (s + 1) l (fun x => f x i j))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j))
        = (∑ a, ∑ b, L2re (pdVec (s + 1) l
              (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
            (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
          + L2re (pdVec (s + 1) l (fun x => Nf x i j))
              (pdVec (s + 1) l (fun x => seriesFunM c x i j)) := by
    intro l
    rw [hpd l]
    exact L2re_sum2_add _ _ _
      (fun a b => (contDiff_pdVec_top ((hAsm a b).mul (hgab a b)) l).continuous)
      (contDiff_pdVec_top (hNfsm i j) l).continuous
      (contDiff_pdVec_top (hSer i j) l).continuous
  have hstep1 : (∑ l : Fin (s + 1) → Fin n,
        L2re (pdVec (s + 1) l (fun x => f x i j))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
      = (∑ l, ∑ a, ∑ b, L2re (pdVec (s + 1) l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        + (∑ l, L2re (pdVec (s + 1) l (fun x => Nf x i j))
            (pdVec (s + 1) l (fun x => seriesFunM c x i j))) := by
    rw [Finset.sum_congr rfl (fun l _ => hl2 l)]
    exact Finset.sum_add_distrib
  have hsplit : ∀ a b : Fin n,
      (∑ l : Fin (s + 1) → Fin n, L2re (pdVec (s + 1) l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        ≤ (∑ l : Fin (s + 1) → Fin n,
            L2re (fun x => A a b x * pdVec (s + 1) l
                (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
              (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
          + |∑ l : Fin (s + 1) → Fin n,
              L2re (fun x => pdVec (s + 1) l (fun y => A a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - A a b x * pdVec (s + 1) l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                (pdVec (s + 1) l (fun x => seriesFunM c x i j))| := by
    intro a b
    have hper : (∑ l : Fin (s + 1) → Fin n, L2re (pdVec (s + 1) l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        = (∑ l, L2re (fun x => A a b x * pdVec (s + 1) l
                (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
              (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
          + (∑ l, L2re (fun x => pdVec (s + 1) l (fun y => A a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - A a b x * pdVec (s + 1) l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                (pdVec (s + 1) l (fun x => seriesFunM c x i j))) := by
      rw [Finset.sum_congr rfl (fun l _ => ?_)]
      · exact Finset.sum_add_distrib
      have hpt : pdVec (s + 1) l (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y)
          = fun x => A a b x * pdVec (s + 1) l
                (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x
              + (pdVec (s + 1) l (fun y => A a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - A a b x * pdVec (s + 1) l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x) := by
        funext x; ring
      conv_lhs => rw [hpt]
      refine L2re_add_left ?_ ?_ ?_
      · exact (hAsm a b).continuous.mul (contDiff_pdVec_top (hgab a b) l).continuous
      · exact ((contDiff_pdVec_top ((hAsm a b).mul (hgab a b)) l).continuous).sub
          ((hAsm a b).continuous.mul (contDiff_pdVec_top (hgab a b) l).continuous)
      · exact (contDiff_pdVec_top (hSer i j) l).continuous
    rw [hper]
    have h := le_abs_self (∑ l : Fin (s + 1) → Fin n, L2re (fun x => pdVec (s + 1) l
          (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y) x
        - A a b x * pdVec (s + 1) l
            (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
      (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
    linarith
  have hgard : (∑ a, ∑ b, ∑ l : Fin (s + 1) → Fin n,
        L2re (fun x => A a b x * pdVec (s + 1) l
            (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
      = ∑ l : Fin (s + 1) → Fin n,
          L2re (fun x => ∑ a, ∑ b, A a b x
              * pd a (pd b (pdVec (s + 1) l (fun x => seriesFunM c x i j))) x)
            (pdVec (s + 1) l (fun x => seriesFunM c x i j)) := by
    rw [sum3_swap]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← L2re_sum2 (fun a b x => A a b x
          * pdVec (s + 1) l (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
        (pdVec (s + 1) l (fun x => seriesFunM c x i j))
        (fun a b => (hAsm a b).continuous.mul (contDiff_pdVec_top (hgab a b) l).continuous)
        (contDiff_pdVec_top (hSer i j) l).continuous]
    congr 1
    funext x
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Work.Diff.STE.cm_pdVec_pd_pd (s + 1) l a b (fun x => seriesFunM c x i j)
      ((hSer i j).of_le (WithTop.coe_le_coe.mpr le_top))]
  calc (∑ l : Fin (s + 1) → Fin n,
        L2re (pdVec (s + 1) l (fun x => f x i j))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
      = (∑ l, ∑ a, ∑ b, L2re (pdVec (s + 1) l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        + (∑ l, L2re (pdVec (s + 1) l (fun x => Nf x i j))
            (pdVec (s + 1) l (fun x => seriesFunM c x i j))) := hstep1
    _ = (∑ a, ∑ b, ∑ l, L2re (pdVec (s + 1) l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        + (∑ l, L2re (pdVec (s + 1) l (fun x => Nf x i j))
            (pdVec (s + 1) l (fun x => seriesFunM c x i j))) := by
        rw [← sum3_swap]
    _ ≤ ((∑ a, ∑ b, ∑ l, L2re (fun x => A a b x * pdVec (s + 1) l
              (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
            (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
          + (∑ a, ∑ b, |∑ l : Fin (s + 1) → Fin n,
              L2re (fun x => pdVec (s + 1) l (fun y => A a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - A a b x * pdVec (s + 1) l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                (pdVec (s + 1) l (fun x => seriesFunM c x i j))|))
        + |∑ l : Fin (s + 1) → Fin n,
            L2re (pdVec (s + 1) l (fun x => Nf x i j))
              (pdVec (s + 1) l (fun x => seriesFunM c x i j))| := by
        have h1 : (∑ a, ∑ b, ∑ l, L2re (pdVec (s + 1) l
              (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
            (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
            ≤ (∑ a, ∑ b, ((∑ l, L2re (fun x => A a b x * pdVec (s + 1) l
                    (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                  (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
                + |∑ l : Fin (s + 1) → Fin n,
                    L2re (fun x => pdVec (s + 1) l (fun y => A a b y
                          * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                        - A a b x * pdVec (s + 1) l
                            (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                      (pdVec (s + 1) l (fun x => seriesFunM c x i j))|)) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hsplit a b))
        rw [sum2_add_distrib'] at h1
        have h2 := le_abs_self (∑ l : Fin (s + 1) → Fin n,
            L2re (pdVec (s + 1) l (fun x => Nf x i j))
              (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        linarith
    _ = _ := by rw [hgard]

end

end Work.Diff.STE.flat
