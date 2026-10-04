/-
# `Work.Diff.STE.flat.pairing_bound`

The static bound on the level-`(s+1)` energy pairing
`Σ_{i,j} [ Σ_l L2re (∂^l (Φ ∘ jet)) (∂^l u_{ij}) + L2re (Φ ∘ jet) u_{ij} ]`

used by the multi-level a priori estimate (`Work.Diff.STE.flat.level_step`).  The proof assembles

* `decomp_pairing_le` (the split into the Gårding, commutator and lower-order parts),
* `pairing_gard_le` (the Gårding dissipation),
* `pairing_rest_le` (absorption of the commutator and lower-order terms),
* `pairing_zero_le` (the zeroth-order term).
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.flat.pairing_decomp
import Submission.Work.Diff.STE.flat.pairing_gard_le
import Submission.Work.Diff.STE.flat.pairing_rest_le
import Submission.Work.Diff.STE.flat.pairing_zero_le
import Submission.Work.Diff.STE.flat.elliptic_inv
import Submission.Work.Diff.STE.flat.inv_jet_bound_symm
import Submission.Work.Diff.STE.flat.nonlin_deriv_bound
import Submission.Work.Diff.STE.flat.Phi_decomp_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

noncomputable section

open Work.Diff.STE.Flat

theorem pairing_bound {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      ∑ i : Fin n, ∑ j : Fin n,
        ((∑ l : Fin (s + 1) → Fin n,
            Work.Diff.STE.L2re
              (Work.Diff.STE.pdVec (s + 1) l (fun x => Φ (x,
                Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j))
              (Work.Diff.STE.pdVec (s + 1) l (fun x =>
                Work.Diff.STE.Flat.seriesFunM c x i j)))
          + Work.Diff.STE.L2re (fun x => Φ (x,
              Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j)
            (fun x => Work.Diff.STE.Flat.seriesFunM c x i j))
        ≤ C * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1) (Work.Diff.STE.Flat.seriesFunM c)) := by
  classical
  obtain ⟨lam', hlam'pos, hellInv⟩ :=
    elliptic_inv (n := n) (s := s) hn hs lam hlam Bs hBs
  obtain ⟨CA, hCAnn, hCAall⟩ :=
    inv_jet_bound_symm (n := n) (s := s) hn hs lam hlam Bs hBs
  obtain ⟨K, Nfun, hKnn, hNsm, hNper, hNdec, hNsup⟩ :=
    nonlin_deriv_bound (n := n) (s := s) hn hs Φ hshape lam hlam Bs hBs
  obtain ⟨Cg, hCgnn, hCg⟩ :=
    pairing_gard_le (n := n) (s := s) hn hs lam hlam Bs hBs lam' hlam'pos
  obtain ⟨Cr, hCrnn, hCr⟩ :=
    pairing_rest_le (n := n) (s := s) hn hs Nfun hNsm lam hlam Bs hBs (lam' / 4)
      (by linarith) K hKnn (fun N c hc hen hell => hNsup N c hc hen hell)
  obtain ⟨Cz, hCznn, hCz⟩ :=
    pairing_zero_le (n := n) (s := s) hn hs Φ Nfun hNdec lam hlam Bs hBs K hKnn
      (fun N c hc hen hell => hNsup N c hc hen hell)
  refine ⟨Cg + (Cr + Cz) + 1, by positivity, ?_⟩
  intro N c hcbox hen hell
  obtain ⟨hCAsm, hCAper, hCAsup, hCAl2, hCApdR⟩ := hCAall N c hcbox hen hell
  have hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun m : Fin n → ℤ => (wt m) ^ M * ‖c m i j‖) :=
    fun i j M => summable_moment_box c hcbox i j M
  have hSer : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j) :=
    fun i j => Work.Diff.STE.contDiff_seriesFun (fun m => c m i j) (hmom i j)
  obtain ⟨hdecomp, hfsm, hfper⟩ :=
    Phi_decomp_smooth Φ Nfun hNdec hNsm hNper hshape.1 hlam hell hmom
  have hNfsm : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => Nfun (x, jetP c x) i j) := by
    intro i j
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => ∑ a, ∑ b, symInvC c a b x
        * pd a (pd b (fun z => seriesFunM c z i j)) x) :=
      ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
        (hCAsm a b).mul (contDiff_pd_top (contDiff_pd_top (hSer i j) b) a)))
    have h3 := (hfsm i j).sub h2
    have h4 : (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM c) x) i j
          - ∑ a, ∑ b, symInvC c a b x * pd a (pd b (fun z => seriesFunM c z i j)) x)
        = fun x => Nfun (x, jetP c x) i j := by
      funext x
      rw [hdecomp x i j]
      ring
    rw [h4] at h3
    exact h3
  -- ### the per-`(i,j)` decomposition
  have hdec : ∀ i j : Fin n,
      (∑ l : Fin (s + 1) → Fin n,
        L2re (pdVec (s + 1) l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        ≤ (∑ l : Fin (s + 1) → Fin n,
            L2re (fun x => ∑ a, ∑ b, symInvC c a b x
                * pd a (pd b (pdVec (s + 1) l (fun x => seriesFunM c x i j))) x)
              (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
          + ((∑ a, ∑ b, |∑ l : Fin (s + 1) → Fin n,
              L2re (fun x => pdVec (s + 1) l (fun y => symInvC c a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - symInvC c a b x * pdVec (s + 1) l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                (pdVec (s + 1) l (fun x => seriesFunM c x i j))|)
            + |∑ l : Fin (s + 1) → Fin n,
                L2re (pdVec (s + 1) l (fun x => Nfun (x, jetP c x) i j))
                  (pdVec (s + 1) l (fun x => seriesFunM c x i j))|) := by
    intro i j
    have h := decomp_pairing_le (s := s) (n := n) (fun x => Φ (x, jetM (seriesFunM c) x))
      (fun x => Nfun (x, jetP c x)) (fun a b => symInvC c a b) c hdecomp hCAsm hNfsm hSer i j
    rw [add_assoc] at h
    exact h
  -- ### the bounds from the three pieces
  have hellInv' : ∀ (x : Fin n → ℝ) (ξ : Fin n → ℝ),
      lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, symInvR c i j x * ξ i * ξ j := by
    intro x ξ
    simpa only [symInvR_apply] using hellInv N c hcbox hen hell x ξ
  have hle2 := hCg N c hcbox hen hell hellInv'
  have hle3 := hCr N c hcbox hen hell
  have hle4 := hCz N c hcbox hen hell
  have hQu_le : ENormSqM (s + 1) (seriesFunM c)
      ≤ ENormSqFull (s + 1) (seriesFunM c) := by
    rw [ENormSqFull]
    linarith [ENormSqM_nonneg 0 (seriesFunM c)]
  have hPtnn : 0 ≤ ENormSqM (s + 2) (seriesFunM c) := ENormSqM_nonneg _ _
  have hEunn : 0 ≤ ENormSqFull (s + 1) (seriesFunM c) := ENormSqFull_nonneg _ _
  have hone : (0 : ℝ) ≤ 1 + ENormSqFull (s + 1) (seriesFunM c) := by linarith
  -- ### splitting the outer double sum
  have houter : (∑ i : Fin n, ∑ j : Fin n,
        ((∑ l : Fin (s + 1) → Fin n,
            L2re (pdVec (s + 1) l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
              (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
          + L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
              (fun x => seriesFunM c x i j)))
      = (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin (s + 1) → Fin n,
            L2re (pdVec (s + 1) l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
              (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        + (∑ i : Fin n, ∑ j : Fin n,
            L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
              (fun x => seriesFunM c x i j)) :=
    sum2_add_distrib' _ _
  rw [houter]
  have hsum1 : (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin (s + 1) → Fin n,
        L2re (pdVec (s + 1) l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
          (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
      ≤ (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin (s + 1) → Fin n,
            L2re (fun x => ∑ a, ∑ b, symInvC c a b x
                * pd a (pd b (pdVec (s + 1) l (fun x => seriesFunM c x i j))) x)
              (pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        + (∑ i : Fin n, ∑ j : Fin n,
            ((∑ a, ∑ b, |∑ l : Fin (s + 1) → Fin n,
                L2re (fun x => pdVec (s + 1) l (fun y => symInvC c a b y
                      * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                    - symInvC c a b x * pdVec (s + 1) l
                        (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                  (pdVec (s + 1) l (fun x => seriesFunM c x i j))|)
              + |∑ l : Fin (s + 1) → Fin n,
                  L2re (pdVec (s + 1) l (fun x => Nfun (x, jetP c x) i j))
                    (pdVec (s + 1) l (fun x => seriesFunM c x i j))|)) := by
    refine (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hdec i j))).trans ?_
    rw [sum2_add_distrib']
  have hsum2 : (∑ i : Fin n, ∑ j : Fin n,
        L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
          (fun x => seriesFunM c x i j))
      ≤ ∑ i : Fin n, ∑ j : Fin n, |L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
          (fun x => seriesFunM c x i j)| :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => le_abs_self _))
  have hmul : Cg * ENormSqM (s + 1) (seriesFunM c)
      ≤ Cg * (1 + ENormSqFull (s + 1) (seriesFunM c)) :=
    mul_le_mul_of_nonneg_left (by linarith) hCgnn
  nlinarith [hsum1, hsum2, hle2, hle3, hle4, hmul, hPtnn, hEunn, hone]

end

end Work.Diff.STE.flat
