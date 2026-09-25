import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder.hSN_bilinear_le
import Submission.Work.CR.Flat.Holder.comp_linear_le
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.NN.Core.holderNorm_bilin_le

/-!
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The pairing `du_z(W z)` in the Hölder scale

For an open `Ω ⊆ ℂⁿ`, a function `u` of class `C^{k,α}` (`k ≥ 1`) on `Ω` and a vector field `W`
whose components have `C^{k-1,α}` seminorm at most `ε` on `Ω`, the function
`z ↦ du_z (W z)` has `C^{k-1,α}` seminorm at most `C ε ‖u‖_{C^{k,α}}` on `Ω`, with a constant
`C` depending only on `n` and `k`.

The point is that the *whole* information available about `W` is the bound `ε` on its
`C^{k-1,α}` norm, and the derivative falling on `u` is one order higher, so that the `ε`-factor
always pairs with the *full* norm of `u` — exactly the shape needed when `W = J - Jstd` is a
small perturbation of the standard complex structure.

Writing `W z = Σ_j Pi.single j (W z j)`, the function is the sum over the coordinates `j` of the
pairings `evalBilin n j (du_z) (W z j) = du_z (Pi.single j (W z j))`; each pairing is bounded and
bilinear of operator norm `≤ 1` in the `(L, c)` variables, so the Leibniz bound
`Work.NN.Core.holderNorm_bilin_le` applies with
`A = ‖u‖_{C^{k,α}}` (through `iDN_fderivWithin`/`hSN_fderivWithin`) and
`E' = ε` (through the hypothesis on `W`), and the finite sum over `j` costs a factor `n`.
-/

namespace Work.NN.Core

open scoped NNReal ENNReal Topology
open Set

open Work.CR.Flat (holderNorm iterDerivNorm holderSeminorm)
open Work.CR.Flat.Holder (iDN hSN iDN_congr hSN_congr iDN_fderivWithin hSN_fderivWithin
  comp_linear_le iDN_complex_eq hSN_complex_eq)

noncomputable section

/-! ### The coordinate evaluation pairing -/

/-- The continuous linear injection `c ↦ Pi.single j c : ℂ → ℂⁿ` (of norm `≤ 1`). -/
private def sVec (n : ℕ) (j : Fin n) : ℂ →L[ℝ] (Cn n) :=
  ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j

private lemma sVec_apply (n : ℕ) (j : Fin n) (c : ℂ) : sVec n j c = Pi.single j c := by
  rw [sVec, ContinuousLinearMap.single_apply]

/-- The bounded bilinear pairing `(L, c) ↦ L (Pi.single j c)`, of operator norm `≤ 1`. -/
private def evalBilin (n : ℕ) (j : Fin n) : (Cn n →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ ℂ (Cn n) ℂ)) (sVec n j)

private lemma evalBilin_apply (n : ℕ) (j : Fin n) (L : Cn n →L[ℝ] ℂ) (c : ℂ) :
    evalBilin n j L c = L (Pi.single j c) := by
  rw [evalBilin, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, sVec_apply]

private lemma norm_evalBilin_le (n : ℕ) (j : Fin n) : ‖evalBilin n j‖ ≤ 1 := by
  have h1 : ‖ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ ℂ (Cn n) ℂ)‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_flip]
    exact ContinuousLinearMap.norm_compL_le ℝ ℂ (Cn n) ℂ
  have h2 : ‖sVec n j‖ ≤ 1 := ContinuousLinearMap.norm_single_le_one ℝ (fun _ : Fin n => ℂ) j
  calc ‖evalBilin n j‖
      = ‖(ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ ℂ (Cn n) ℂ)) (sVec n j)‖ := rfl
    _ ≤ ‖ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ ℂ (Cn n) ℂ)‖ * ‖sVec n j‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

/-- `holderNorm` depends only on the values of the function on `Ω`. -/
private lemma holderNorm_congrOn {n : ℕ} {k : ℕ} {α : ℝ} {f g : Cn n → ℂ} {Ω : Set (Cn n)}
    (h : ∀ x ∈ Ω, f x = g x) : holderNorm k α f Ω = holderNorm k α g Ω := by
  unfold Work.CR.Flat.holderNorm
  exact Finset.sum_congr rfl fun i _ => by
    have h1 : iterDerivNorm i f Ω = iterDerivNorm i g Ω := iDN_congr h
    have h2 : holderSeminorm i α f Ω = holderSeminorm i α g Ω := hSN_congr h
    rw [h1, h2]

/-- The pointwise decomposition of `du_z(w)` along the coordinates:
`du_z w = Σ_j (du_z) (Pi.single j (w j))`. -/
private lemma fderivWithin_apply_eq_sum (n : ℕ) (u : Cn n → ℂ) (Ω : Set (Cn n)) (z : Cn n)
    (w : Cn n) :
    fderivWithin ℝ u Ω z w = ∑ j : Fin n, evalBilin n j (fderivWithin ℝ u Ω z) (w j) := by
  have harg : (∑ j : Fin n, Pi.single j (w j)) = w := Finset.univ_sum_single w
  calc fderivWithin ℝ u Ω z w
      = fderivWithin ℝ u Ω z (∑ j : Fin n, Pi.single j (w j)) := by rw [harg]
    _ = ∑ j : Fin n, fderivWithin ℝ u Ω z (Pi.single j (w j)) := map_sum _ _ _
    _ = ∑ j : Fin n, evalBilin n j (fderivWithin ℝ u Ω z) (w j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [evalBilin_apply]

/-! ### The main estimate -/

lemma holderNorm_fderiv_apply_le {n : ℕ} {α : ℝ} (hα : 0 < α) {Ω : Set (Work.NN.Core.Cn n)}
    (hΩ : IsOpen Ω) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) u Ω)
        {W : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
        (hW : ∀ j, ContDiffOn ℝ (((k-1 : ℕ)) : WithTop ℕ∞) (fun z => W z j) Ω)
        {ε : ℝ} (hε : 0 ≤ ε)
        (hb : ∀ j, Work.CR.Flat.holderNorm (k-1) α (fun z => W z j) Ω ≤ ENNReal.ofReal ε),
      Work.CR.Flat.holderNorm (k-1) α (fun z => fderiv ℝ u z (W z)) Ω
        ≤ ENNReal.ofReal C * (ENNReal.ofReal ε * Work.CR.Flat.holderNorm k α u Ω) := by
  refine ⟨(n : ℝ) * (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1)) + 1, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ (n : ℝ) * (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1)) := by positivity
    linarith
  · intro u hu W hW ε hε hb
    -- `fderivWithin ℝ u Ω` is `C^{k-1}` and `Ω` is a uniqueness domain.
    have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
    have hmk : ((k - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((k : ℕ) : WithTop ℕ∞) := by
      have h : k - 1 + 1 ≤ k := (Nat.sub_add_cancel hk).le
      exact_mod_cast h
    have hfd : ContDiffOn ℝ (((k - 1 : ℕ)) : ℕ∞) (fun z => fderivWithin ℝ u Ω z) Ω :=
      hu.fderivWithin hΩu hmk
    -- the pointwise decomposition of the function
    have hpt : ∀ z ∈ Ω, fderivWithin ℝ u Ω z (W z)
        = ∑ j : Fin n, evalBilin n j (fderivWithin ℝ u Ω z) (W z j) :=
      fun z _ => fderivWithin_apply_eq_sum n u Ω z (W z)
    -- the two bounds entering the bilinear Leibniz estimate
    have hA_le : ∀ l, l ≤ k - 1 →
        iDN l (fun z => fderivWithin ℝ u Ω z) Ω
          + hSN l α (fun z => fderivWithin ℝ u Ω z) Ω ≤ holderNorm k α u Ω := by
      intro l hl
      have hl1 : l + 1 ≤ k := by omega
      rw [iDN_fderivWithin l u Ω hΩu, hSN_fderivWithin l α u Ω hΩu, iDN_complex_eq,
        hSN_complex_eq]
      exact Finset.single_le_sum (f := fun i => iterDerivNorm i u Ω + holderSeminorm i α u Ω)
        (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl1))
    have hE_le : ∀ (j : Fin n) (l : ℕ), l ≤ k - 1 →
        iDN l (fun z => W z j) Ω + hSN l α (fun z => W z j) Ω ≤ ENNReal.ofReal ε := by
      intro j l hl
      refine le_trans ?_ (hb j)
      exact Finset.single_le_sum
        (f := fun i => iDN i (fun z => W z j) Ω + hSN i α (fun z => W z j) Ω)
        (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
    have hFj : ∀ j : Fin n, ContDiffOn ℝ (((k - 1 : ℕ)) : ℕ∞)
        (fun z => evalBilin n j (fderivWithin ℝ u Ω z) (W z j)) Ω := by
      intro j
      exact ContDiffOn.clm_apply ((evalBilin n j).contDiff.comp_contDiffOn hfd) (hW j)
    -- the estimate for each coordinate
    have hcompj : ∀ j : Fin n,
        holderNorm (k - 1) α (fun z => evalBilin n j (fderivWithin ℝ u Ω z) (W z j)) Ω
          ≤ ENNReal.ofReal (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1))
              * (holderNorm k α u Ω * ENNReal.ofReal ε) := by
      intro j
      have hbil := holderNorm_bilin_le (m := k - 1) (α := α) (B := evalBilin n j)
        (f := fun z => fderivWithin ℝ u Ω z) (g := fun z => W z j) (Ω := Ω)
        hfd (hW j) hΩu hA_le (hE_le j)
      refine le_trans hbil ?_
      have h1 : ENNReal.ofReal ‖evalBilin n j‖ ≤ 1 :=
        ENNReal.ofReal_le_one.mpr (norm_evalBilin_le n j)
      calc ENNReal.ofReal ‖evalBilin n j‖
            * (ENNReal.ofReal (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1))
                * (holderNorm k α u Ω * ENNReal.ofReal ε))
          ≤ 1 * (ENNReal.ofReal (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1))
                * (holderNorm k α u Ω * ENNReal.ofReal ε)) := by
            exact mul_le_mul_left h1 _
        _ = ENNReal.ofReal (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1))
                * (holderNorm k α u Ω * ENNReal.ofReal ε) := one_mul _
    -- replace `fderiv` by `fderivWithin` and split into the coordinates
    have hcongr1 : holderNorm (k - 1) α (fun z => fderiv ℝ u z (W z)) Ω
        = holderNorm (k - 1) α (fun z => fderivWithin ℝ u Ω z (W z)) Ω :=
      holderNorm_congrOn (fun z hz => by rw [fderivWithin_of_isOpen hΩ hz])
    have hcongr2 : holderNorm (k - 1) α (fun z => fderivWithin ℝ u Ω z (W z)) Ω
        = holderNorm (k - 1) α
            (fun z => ∑ j : Fin n, evalBilin n j (fderivWithin ℝ u Ω z) (W z j)) Ω :=
      holderNorm_congrOn hpt
    rw [hcongr1, hcongr2]
    calc holderNorm (k - 1) α
          (fun z => ∑ j : Fin n, evalBilin n j (fderivWithin ℝ u Ω z) (W z j)) Ω
        ≤ ∑ j : Fin n, holderNorm (k - 1) α
            (fun z => evalBilin n j (fderivWithin ℝ u Ω z) (W z j)) Ω :=
          Work.CR.Flat.Holder.holderNorm_sum_le Finset.univ (fun j _ => hFj j) hΩu
      _ ≤ ∑ j : Fin n, ENNReal.ofReal (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1))
            * (holderNorm k α u Ω * ENNReal.ofReal ε) :=
          Finset.sum_le_sum (fun j _ => hcompj j)
      _ = (n : ENNReal) * (ENNReal.ofReal (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1))
            * (holderNorm k α u Ω * ENNReal.ofReal ε)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal ((n : ℝ) * (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1)))
            * (holderNorm k α u Ω * ENNReal.ofReal ε) := by
          rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((n : ℝ) * (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1)))
            * (ENNReal.ofReal ε * holderNorm k α u Ω) := by
          rw [mul_comm (holderNorm k α u Ω) (ENNReal.ofReal ε)]
      _ ≤ ENNReal.ofReal ((n : ℝ) * (3 * (((k - 1 : ℕ) : ℝ) + 1) * 2 ^ (k - 1)) + 1)
            * (ENNReal.ofReal ε * holderNorm k α u Ω) := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          exact le_add_of_nonneg_right zero_le_one

end

end Work.NN.Core
