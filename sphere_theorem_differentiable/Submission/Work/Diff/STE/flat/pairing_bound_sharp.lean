/-
# Assembly of `Work.Diff.STE.flat.PairingBoundSharp` from its four pieces

`PairingBoundSharp` is the single analytic input of the flat `Hᵏ` a priori estimate.  It is
assembled here from

* `Work.Diff.STE.flat.pairing_gard_sharp`  -- the Gårding dissipation,
* `Work.Diff.STE.flat.comm_sharp_bound`    -- the Leibniz commutator correction,
* `Work.Diff.STE.flat.pairing_N_sharp`     -- the lower-order (`Nfun`) term,
* `Work.Diff.STE.flat.pairing_zero_sharp`  -- the zeroth-order term,

together with the level-`k` decomposition `decomp_pairing_le_k` (a copy of
`Work.Diff.STE.flat.decomp_pairing_le` at level `k` instead of `s + 1`) and the absorption
`√(1 + E) ≤ ε E + (ε + 1/(4ε))`.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.pairing_sharp
import Submission.Work.Diff.STE.flat.pairing_sharp_core
import Submission.Work.Diff.STE.flat.comm_sharp_bound
import Submission.Work.Diff.STE.flat.phi_bound_nosym
import Submission.Work.Diff.STE.flat.symInv_garding_bounds
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.flat.Phi_decomp_smooth
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.commutator_pd
import Submission.Work.Diff.STE.fourierCoeff_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

noncomputable section

open Work.Diff.STE.Flat

/-! ## The level-`k` decomposition of the pairing -/

lemma sum2_add_distrib'k {ι κ : Type*} [Fintype ι] [Fintype κ] (F G : ι → κ → ℝ) :
    (∑ a, ∑ b, (F a b + G a b)) = (∑ a, ∑ b, F a b) + (∑ a, ∑ b, G a b) := by
  simp only [Finset.sum_add_distrib]

/-- Cyclic swap of a triple sum. -/
lemma sum3_swap_k {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (H : ι → κ → τ → ℝ) : (∑ a, ∑ b, ∑ l, H a b l) = ∑ l, ∑ a, ∑ b, H a b l := by
  rw [← Fintype.sum_prod_type (f := fun p : ι × κ => ∑ l, H p.1 p.2 l)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  exact Fintype.sum_prod_type (f := fun p : ι × κ => H p.1 p.2 l)

/-! ## The decomposition of the pairing -/

/-- **The decomposition of the level-`k` pairing** (the level-`k` case of
`Work.Diff.STE.flat.decomp_pairing_le`).**  Splits the pairing of the nonlinearity
into the Gårding (principal) part, the Leibniz commutator corrections and the lower-order term. -/
lemma decomp_pairing_le_k {n k : ℕ} (f : (Fin n → ℝ) → MatC n) (Nf : (Fin n → ℝ) → MatC n)
    (A : Fin n → Fin n → (Fin n → ℝ) → ℂ) (c : (Fin n → ℤ) → MatC n)
    (hdec : ∀ (x : Fin n → ℝ) (i j : Fin n),
      f x i j = (∑ a, ∑ b, A a b x * pd a (pd b (fun z => seriesFunM c z i j)) x) + Nf x i j)
    (hAsm : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b))
    (hNfsm : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => Nf x i j))
    (hSer : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j))
    (i j : Fin n) :
    (∑ l : Fin k → Fin n,
        L2re (pdVec k l (fun x => f x i j))
          (pdVec k l (fun x => seriesFunM c x i j)))
      ≤ (∑ l : Fin k → Fin n,
          L2re (fun x => ∑ a, ∑ b, A a b x
              * pd a (pd b (pdVec k l (fun x => seriesFunM c x i j))) x)
            (pdVec k l (fun x => seriesFunM c x i j)))
        + (∑ a, ∑ b, |∑ l : Fin k → Fin n,
            L2re (fun x => pdVec k l (fun y => A a b y
                  * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                - A a b x * pdVec k l
                    (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
              (pdVec k l (fun x => seriesFunM c x i j))|)
        + |∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Nf x i j))
              (pdVec k l (fun x => seriesFunM c x i j))| := by
  classical
  have hgab : ∀ a b : Fin n,
      ContDiff ℝ (⊤ : ℕ∞) (fun y => pd a (pd b (fun z => seriesFunM c z i j)) y) :=
    fun a b => contDiff_pd_top (contDiff_pd_top (hSer i j) b) a
  have hf : (fun x : Fin n → ℝ => f x i j)
      = fun x => (∑ a, ∑ b, A a b x * pd a (pd b (fun z => seriesFunM c z i j)) x)
          + Nf x i j := by
    funext x; exact hdec x i j
  have hpd : ∀ l : Fin k → Fin n,
      pdVec k l (fun x => f x i j)
        = fun x => (∑ a, ∑ b, pdVec k l
              (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y) x)
          + pdVec k l (fun x => Nf x i j) x := by
    intro l
    rw [hf]
    exact pdVec_sum2_add l (fun a b y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y)
      (fun x => Nf x i j) (fun a b => (hAsm a b).mul (hgab a b)) (hNfsm i j)
  have hl2 : ∀ l : Fin k → Fin n,
      L2re (pdVec k l (fun x => f x i j))
          (pdVec k l (fun x => seriesFunM c x i j))
        = (∑ a, ∑ b, L2re (pdVec k l
              (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
            (pdVec k l (fun x => seriesFunM c x i j)))
          + L2re (pdVec k l (fun x => Nf x i j))
              (pdVec k l (fun x => seriesFunM c x i j)) := by
    intro l
    rw [hpd l]
    exact L2re_sum2_add _ _ _
      (fun a b => (contDiff_pdVec_top ((hAsm a b).mul (hgab a b)) l).continuous)
      (contDiff_pdVec_top (hNfsm i j) l).continuous
      (contDiff_pdVec_top (hSer i j) l).continuous
  have hstep1 : (∑ l : Fin k → Fin n,
        L2re (pdVec k l (fun x => f x i j))
          (pdVec k l (fun x => seriesFunM c x i j)))
      = (∑ l, ∑ a, ∑ b, L2re (pdVec k l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec k l (fun x => seriesFunM c x i j)))
        + (∑ l, L2re (pdVec k l (fun x => Nf x i j))
            (pdVec k l (fun x => seriesFunM c x i j))) := by
    rw [Finset.sum_congr rfl (fun l _ => hl2 l)]
    exact Finset.sum_add_distrib
  have hsplit : ∀ a b : Fin n,
      (∑ l : Fin k → Fin n, L2re (pdVec k l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec k l (fun x => seriesFunM c x i j)))
        ≤ (∑ l : Fin k → Fin n,
            L2re (fun x => A a b x * pdVec k l
                (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
              (pdVec k l (fun x => seriesFunM c x i j)))
          + |∑ l : Fin k → Fin n,
              L2re (fun x => pdVec k l (fun y => A a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - A a b x * pdVec k l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                (pdVec k l (fun x => seriesFunM c x i j))| := by
    intro a b
    have hper : (∑ l : Fin k → Fin n, L2re (pdVec k l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec k l (fun x => seriesFunM c x i j)))
        = (∑ l, L2re (fun x => A a b x * pdVec k l
                (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
              (pdVec k l (fun x => seriesFunM c x i j)))
          + (∑ l, L2re (fun x => pdVec k l (fun y => A a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - A a b x * pdVec k l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                (pdVec k l (fun x => seriesFunM c x i j))) := by
      rw [Finset.sum_congr rfl (fun l _ => ?_)]
      · exact Finset.sum_add_distrib
      have hpt : pdVec k l (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y)
          = fun x => A a b x * pdVec k l
                (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x
              + (pdVec k l (fun y => A a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - A a b x * pdVec k l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x) := by
        funext x; ring
      conv_lhs => rw [hpt]
      refine L2re_add_left ?_ ?_ ?_
      · exact (hAsm a b).continuous.mul (contDiff_pdVec_top (hgab a b) l).continuous
      · exact ((contDiff_pdVec_top ((hAsm a b).mul (hgab a b)) l).continuous).sub
          ((hAsm a b).continuous.mul (contDiff_pdVec_top (hgab a b) l).continuous)
      · exact (contDiff_pdVec_top (hSer i j) l).continuous
    rw [hper]
    have h := le_abs_self (∑ l : Fin k → Fin n, L2re (fun x => pdVec k l
          (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y) x
        - A a b x * pdVec k l
            (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
      (pdVec k l (fun x => seriesFunM c x i j)))
    linarith
  have hgard : (∑ a, ∑ b, ∑ l : Fin k → Fin n,
        L2re (fun x => A a b x * pdVec k l
            (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
          (pdVec k l (fun x => seriesFunM c x i j)))
      = ∑ l : Fin k → Fin n,
          L2re (fun x => ∑ a, ∑ b, A a b x
              * pd a (pd b (pdVec k l (fun x => seriesFunM c x i j))) x)
            (pdVec k l (fun x => seriesFunM c x i j)) := by
    rw [sum3_swap_k]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← L2re_sum2 (fun a b x => A a b x
          * pdVec k l (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
        (pdVec k l (fun x => seriesFunM c x i j))
        (fun a b => (hAsm a b).continuous.mul (contDiff_pdVec_top (hgab a b) l).continuous)
        (contDiff_pdVec_top (hSer i j) l).continuous]
    congr 1
    funext x
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Work.Diff.STE.cm_pdVec_pd_pd k l a b (fun x => seriesFunM c x i j)
      ((hSer i j).of_le (WithTop.coe_le_coe.mpr le_top))]
  calc (∑ l : Fin k → Fin n,
        L2re (pdVec k l (fun x => f x i j))
          (pdVec k l (fun x => seriesFunM c x i j)))
      = (∑ l, ∑ a, ∑ b, L2re (pdVec k l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec k l (fun x => seriesFunM c x i j)))
        + (∑ l, L2re (pdVec k l (fun x => Nf x i j))
            (pdVec k l (fun x => seriesFunM c x i j))) := hstep1
    _ = (∑ a, ∑ b, ∑ l, L2re (pdVec k l
            (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
          (pdVec k l (fun x => seriesFunM c x i j)))
        + (∑ l, L2re (pdVec k l (fun x => Nf x i j))
            (pdVec k l (fun x => seriesFunM c x i j))) := by
        rw [← sum3_swap_k]
    _ ≤ ((∑ a, ∑ b, ∑ l, L2re (fun x => A a b x * pdVec k l
              (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
            (pdVec k l (fun x => seriesFunM c x i j)))
          + (∑ a, ∑ b, |∑ l : Fin k → Fin n,
              L2re (fun x => pdVec k l (fun y => A a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - A a b x * pdVec k l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                (pdVec k l (fun x => seriesFunM c x i j))|))
        + |∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Nf x i j))
              (pdVec k l (fun x => seriesFunM c x i j))| := by
        have h1 : (∑ a, ∑ b, ∑ l, L2re (pdVec k l
              (fun y => A a b y * pd a (pd b (fun z => seriesFunM c z i j)) y))
            (pdVec k l (fun x => seriesFunM c x i j)))
            ≤ (∑ a, ∑ b, ((∑ l, L2re (fun x => A a b x * pdVec k l
                    (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                  (pdVec k l (fun x => seriesFunM c x i j)))
                + |∑ l : Fin k → Fin n,
                    L2re (fun x => pdVec k l (fun y => A a b y
                          * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                        - A a b x * pdVec k l
                            (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                      (pdVec k l (fun x => seriesFunM c x i j))|)) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hsplit a b))
        rw [sum2_add_distrib'k] at h1
        have h2 := le_abs_self (∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Nf x i j))
              (pdVec k l (fun x => seriesFunM c x i j)))
        linarith
    _ = _ := by rw [hgard]

/-! ## Periodicity helpers -/

private lemma periodic1_sum {n : ℕ} {ι' : Type*} [Fintype ι']
    {g : ι' → (Fin n → ℝ) → ℂ} (hg : ∀ a, Periodic1 (g a)) :
    Periodic1 (fun x => ∑ a, g a x) := by
  intro i x
  simp only [Pi.add_apply]
  exact Finset.sum_congr rfl (fun a _ => hg a i x)

private lemma periodic1_mul {n : ℕ} {f g : (Fin n → ℝ) → ℂ}
    (hf : Periodic1 f) (hg : Periodic1 g) : Periodic1 (fun x => f x * g x) := by
  intro i x
  simp only [Pi.add_apply]
  rw [hf i x, hg i x]

private lemma periodic1_pd {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Periodic1 f) (j : Fin n) :
    Periodic1 (pd j f) :=
  fun i x => Work.Diff.STE.periodicIn_pd_of_differentiable i j
    (hf.differentiable (by simp)) (hper i) x

/-! ## The assembly -/

/-- **`Work.Diff.STE.flat.PairingBoundSharp` at the sharp threshold.**  This is the single
analytic input of `Work.Diff.STE.flat.energy_apriori`.

The four pieces are summed (the level-`k` part is split by `decomp_pairing_le_k` into the Gårding,
commutator and `Nfun` contributions) and the two square-root terms are absorbed against the
Gårding dissipation via `√(1 + E) ≤ ε E + (ε + 1/(4ε))` with `ε = lam'/(16 (Cn + Cz + 1))`. -/
theorem pairingBoundSharp_of_pieces {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hshape : IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    PairingBoundSharp n k Φ hshape lam B := by
  classical
  obtain ⟨lam', hlam', Cd, hCd, hgb⟩ := symInv_garding_bounds hn k hk lam hlam B hB
  obtain ⟨Cg, hCg, hgard⟩ := pairing_gard_sharp hn k hk lam hlam B hB lam' hlam'
  obtain ⟨Cc, hCc, hcomm⟩ := Work.Diff.STE.flat.comm_sharp_bound hn k hk lam hlam B hB lam' hlam'
  obtain ⟨Cz, hCz, hzero⟩ := pairing_zero_sharp hn k hk Φ hshape lam hlam B hB
  obtain ⟨hΦsm, Nfun, hNsm, hNdec, hNper⟩ := hshape
  obtain ⟨Cn, hCn, hN⟩ := pairing_N_sharp hn k hk Nfun hNsm hNper lam hlam B hB
  -- the absorption constant: the two square-root terms are priced against the dissipation
  set Ctot : ℝ := (Cn + Cz) * Real.sqrt (1 + B ^ 2) with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by rw [hCtotdef]; positivity
  set eps : ℝ := lam' / (16 * (Ctot + 1)) with hepsdef
  have heps0 : 0 < eps := by rw [hepsdef]; positivity
  have heps_le : Ctot * eps ≤ lam' / 16 := by
    rw [hepsdef, mul_div, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 16)]
    nlinarith [hlam', hCtot0]
  refine ⟨Cg + Cc + Ctot * (eps + 1 / (4 * eps)) + 1, by positivity, ?_⟩
  intro N c hc hen hell
  -- the Gårding bounds, needed for smoothness/periodicity of the principal coefficient
  obtain ⟨hsmR, hsmC, hperR, hperC, hpdr, hell'⟩ := hgb N c hc hen hell
  have hSer : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => seriesFunM c x i j) :=
    fun i j => Work.Diff.STE.contDiff_seriesFun (c := fun k' : Fin n → ℤ => c k' i j)
      (fun M' => summable_moment_box c hc i j M')
  have hSerper : ∀ i j : Fin n, Periodic1 (fun x => seriesFunM c x i j) := by
    intro i j
    have h := Work.Diff.STE.periodic_seriesFun (fun k' : Fin n → ℤ => c k' i j)
    simpa only [seriesFunM_apply] using h
  -- the pointwise decomposition of the nonlinearity
  obtain ⟨hdec, hfsm, hfper⟩ := Phi_decomp_smooth (c := c) Φ Nfun hNdec hNsm hNper hΦsm hlam hell
    (fun i j M' => summable_moment_box c hc i j M')
  -- smoothness of the lower-order term
  have hPsm : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ a, ∑ b, symInvC c a b x
      * pd a (pd b (fun z => seriesFunM c z i j)) x) := by
    intro i j
    refine ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_
    exact (hsmC a b).mul (contDiff_pd_top (contDiff_pd_top (hSer i j) b) a)
  have hNfsm : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x => Nfun (x, jetP c x) i j) := by
    intro i j
    have hdiff : ContDiff ℝ (⊤ : ℕ∞) (fun x => Φ (x, jetM (seriesFunM c) x) i j
        - ∑ a, ∑ b, symInvC c a b x * pd a (pd b (fun z => seriesFunM c z i j)) x) :=
      (hfsm i j).sub (hPsm i j)
    have hfun : (fun x => Φ (x, jetM (seriesFunM c) x) i j
          - ∑ a, ∑ b, symInvC c a b x * pd a (pd b (fun z => seriesFunM c z i j)) x)
        = fun x => Nfun (x, jetP c x) i j := by
      funext x
      rw [hdec x i j]
      ring
    rwa [hfun] at hdiff
  -- periodicity of the lower-order term
  have hPper : ∀ i j : Fin n, Periodic1 (fun x => ∑ a, ∑ b, symInvC c a b x
      * pd a (pd b (fun z => seriesFunM c z i j)) x) := by
    intro i j
    refine periodic1_sum fun a => periodic1_sum fun b => ?_
    refine periodic1_mul (hperC a b) ?_
    exact periodic1_pd (contDiff_pd_top (hSer i j) b)
      (periodic1_pd (hSer i j) (hSerper i j) b) a
  have hNper' : ∀ i j : Fin n, Periodic1 (fun x => Nfun (x, jetP c x) i j) := by
    intro i j
    have hfun : (fun x => Φ (x, jetM (seriesFunM c) x) i j
          - ∑ a, ∑ b, symInvC c a b x * pd a (pd b (fun z => seriesFunM c z i j)) x)
        = fun x => Nfun (x, jetP c x) i j := by
      funext x
      rw [hdec x i j]
      ring
    rw [← hfun]
    intro k' x
    simp only [Pi.sub_apply]
    rw [show Φ (x + Pi.single k' 1, jetM (seriesFunM c) (x + Pi.single k' 1)) i j
          = Φ (x, jetM (seriesFunM c) x) i j from hfper i j k' x,
      show (∑ a, ∑ b, symInvC c a b (x + Pi.single k' 1)
              * pd a (pd b (fun z => seriesFunM c z i j)) (x + Pi.single k' 1))
            = ∑ a, ∑ b, symInvC c a b x * pd a (pd b (fun z => seriesFunM c z i j)) x
          from hPper i j k' x]
  -- the level-`k` decomposition, summed over the indices
  have hAij : ∀ i j : Fin n,
      (∑ l : Fin k → Fin n, L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
          (pdVec k l (fun x => seriesFunM c x i j)))
        ≤ (∑ l : Fin k → Fin n,
            L2re (fun x => ∑ a, ∑ b, symInvC c a b x
                * pd a (pd b (pdVec k l (fun y => seriesFunM c y i j))) x)
              (pdVec k l (fun y => seriesFunM c y i j)))
          + (∑ a, ∑ b, |∑ l : Fin k → Fin n,
              L2re (fun x => pdVec k l (fun y => symInvC c a b y
                    * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                  - symInvC c a b x * pdVec k l
                      (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
                (pdVec k l (fun x => seriesFunM c x i j))|)
          + |∑ l : Fin k → Fin n,
              L2re (pdVec k l (fun x => Nfun (x, jetP c x) i j))
                (pdVec k l (fun x => seriesFunM c x i j))| :=
    fun i j => decomp_pairing_le_k (n := n) (k := k)
      (f := fun x => Φ (x, jetM (seriesFunM c) x))
      (Nf := fun x i j => Nfun (x, jetP c x) i j)
      (A := fun a b => symInvC c a b) (c := c) hdec hsmC hNfsm hSer i j
  have hAk : (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
        L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
          (pdVec k l (fun x => seriesFunM c x i j)))
      ≤ (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
          L2re (fun x => ∑ a, ∑ b, symInvC c a b x
              * pd a (pd b (pdVec k l (fun y => seriesFunM c y i j))) x)
            (pdVec k l (fun y => seriesFunM c y i j)))
        + (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n, |∑ l : Fin k → Fin n,
            L2re (fun x => pdVec k l (fun y => symInvC c a b y
                  * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                - symInvC c a b x * pdVec k l
                    (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
              (pdVec k l (fun x => seriesFunM c x i j))|)
        + (∑ i : Fin n, ∑ j : Fin n, |∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Nfun (x, jetP c x) i j))
              (pdVec k l (fun x => seriesFunM c x i j))|) := by
    have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hAij i j
    refine h1.trans ?_
    simp only [Finset.sum_add_distrib]
    exact le_of_eq (by abel)
  -- the zeroth order part
  have hZ : (∑ i : Fin n, ∑ j : Fin n,
        L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j) (fun x => seriesFunM c x i j))
      ≤ Cz * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) :=
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => le_abs_self _).trans
      (hzero N c hc hen hell)
  -- the three pieces of the level-`k` part
  have hGard := hgard N c hc hen hell hell'
  have hComm := hcomm N c hc hen hell fun x ξ => hell' x ξ
  have hNterm := hN N c hc hen hell hNfsm hNper'
  -- the absorption
  have hEM0 : 0 ≤ ENormSqM (k + 1) (seriesFunM c) := ENormSqM_nonneg (k + 1) _
  have hE0B : ENormSqM 0 (seriesFunM c) ≤ B ^ 2 :=
    (ENormSqM_zero_le_ENormSqFull k (seriesFunM c)).trans hen
  have hEdec : ENormSqFull (k + 1) (seriesFunM c)
      = ENormSqM (k + 1) (seriesFunM c) + ENormSqM 0 (seriesFunM c) := rfl
  -- `√(1 + E_full) ≤ √(1 + B²) √(1 + E_{k+1})`
  have hEsq : 1 + ENormSqFull (k + 1) (seriesFunM c)
      ≤ (1 + B ^ 2) * (1 + ENormSqM (k + 1) (seriesFunM c)) := by
    rw [hEdec]
    nlinarith [hE0B, hB]
  have hsqrtE : (Cn + Cz) * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))
      ≤ Ctot * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c)) := by
    have h1 : Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))
        ≤ Real.sqrt (1 + B ^ 2) * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c)) := by
      calc Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))
          ≤ Real.sqrt ((1 + B ^ 2) * (1 + ENormSqM (k + 1) (seriesFunM c))) :=
            Real.sqrt_le_sqrt hEsq
        _ = Real.sqrt (1 + B ^ 2) * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c)) := by
            rw [Real.sqrt_mul (by positivity)]
    rw [hCtotdef, mul_assoc]
    refine mul_le_mul_of_nonneg_left h1 (by positivity)
  -- the elementary absorption `√(1 + X) ≤ ε X + (ε + 1/(4ε))`
  have habs : ∀ X : ℝ, 0 ≤ X →
      Real.sqrt (1 + X) ≤ eps * X + (eps + 1 / (4 * eps)) := by
    intro X hX
    have h1 : (0 : ℝ) ≤ 1 + X := by linarith
    have hsq := Real.sq_sqrt h1
    have h4 : 4 * eps * Real.sqrt (1 + X) ≤ 4 * eps ^ 2 * (1 + X) + 1 := by
      nlinarith [sq_nonneg (2 * eps * Real.sqrt (1 + X) - 1), hsq, heps0]
    have h5 : Real.sqrt (1 + X) ≤ (4 * eps ^ 2 * (1 + X) + 1) / (4 * eps) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * eps)]
      linarith [h4]
    have h6 : (4 * eps ^ 2 * (1 + X) + 1) / (4 * eps) = eps * (1 + X) + 1 / (4 * eps) := by
      field_simp
    linarith [h5, h6]
  have hkey : Ctot * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c))
      ≤ Ctot * (eps + 1 / (4 * eps)) + (lam' / 16) * ENormSqM (k + 1) (seriesFunM c) := by
    have h1 : Ctot * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c))
        ≤ Ctot * (eps * ENormSqM (k + 1) (seriesFunM c) + (eps + 1 / (4 * eps))) :=
      mul_le_mul_of_nonneg_left (habs _ hEM0) hCtot0
    have h2 : Ctot * (eps * ENormSqM (k + 1) (seriesFunM c))
        ≤ (lam' / 16) * ENormSqM (k + 1) (seriesFunM c) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right heps_le hEM0
    linarith [h1, h2]
  -- the final estimate
  have hfin : pairSharp n k Φ c
      ≤ Cg + Cc + Ctot * (eps + 1 / (4 * eps)) + 1 := by
    have hsplit : pairSharp n k Φ c
        = (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
              (pdVec k l (fun x => seriesFunM c x i j)))
          + (∑ i : Fin n, ∑ j : Fin n,
              L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
                (fun x => seriesFunM c x i j)) := by
      simp only [pairSharp, Finset.sum_add_distrib]
    rw [hsplit]
    have hstep : (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
              (pdVec k l (fun x => seriesFunM c x i j)))
          + (∑ i : Fin n, ∑ j : Fin n,
              L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
                (fun x => seriesFunM c x i j))
        ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
          + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
          + ((Cn + Cz) * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))) := by
      have h1 : (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
            L2re (pdVec k l (fun x => Φ (x, jetM (seriesFunM c) x) i j))
              (pdVec k l (fun x => seriesFunM c x i j)))
          ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
            + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
            + (Cn * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))) := by
        linarith [hAk, hGard, hComm, hNterm]
      have h2 : (∑ i : Fin n, ∑ j : Fin n,
            L2re (fun x => Φ (x, jetM (seriesFunM c) x) i j)
              (fun x => seriesFunM c x i j))
          ≤ Cz * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c)) := hZ
      linarith [h1, h2]
    calc _ ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
          + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
          + ((Cn + Cz) * Real.sqrt (1 + ENormSqFull (k + 1) (seriesFunM c))) := hstep
      _ ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
          + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
          + (Ctot * Real.sqrt (1 + ENormSqM (k + 1) (seriesFunM c))) := by
            linarith [hsqrtE]
      _ ≤ (-(lam' / 2) * ENormSqM (k + 1) (seriesFunM c) + Cg)
          + ((lam' / 8) * ENormSqM (k + 1) (seriesFunM c) + Cc)
          + (Ctot * (eps + 1 / (4 * eps))
            + (lam' / 16) * ENormSqM (k + 1) (seriesFunM c)) := by linarith [hkey]
      _ ≤ Cg + Cc + Ctot * (eps + 1 / (4 * eps)) + 1 := by
        have h3 : -(lam' / 2) * ENormSqM (k + 1) (seriesFunM c)
            + (lam' / 8) * ENormSqM (k + 1) (seriesFunM c)
            + (lam' / 16) * ENormSqM (k + 1) (seriesFunM c) ≤ 0 :=
          by nlinarith [hEM0, hlam']
        linarith [h3]
  exact hfin

end

end Work.Diff.STE.flat
