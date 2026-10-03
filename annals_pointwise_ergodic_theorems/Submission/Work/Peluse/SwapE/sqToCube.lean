import Mathlib
import Submission.Work.Peluse.SwapE.Reduce
import Submission.Work.Peluse.PET.boxNormPow_scale_transfer
import Submission.Work.Peluse.SwapE.cubeMass.fiberSum
import Submission.Work.Peluse.SwapE.cubeMass.sumTdirCons
import Submission.Work.Peluse.SwapE.cubeMass.fejerId
import Submission.Work.Peluse.SwapE.cubeMass.fejerCS
import Submission.Work.Peluse.SwapE.cubeMass.massSq_le
import Submission.Work.Peluse.SwapE.cubeMass.Split

/-!
# `SwapE/sqToCube` — the mean square of the cube mass controls the box-norm power

This module proves `Work.Peluse.SwapE.SqToCube`, the analytic heart of the endgame node
(`SwapE/NOTES_SwapE.md`, KKL arXiv:2407.08636 §8, the passage from (57) to the end of the proof of
Theorem 1.10).

## The statement

For a `1`-bounded `f` supported in `symIcc N` and `θ ≤ massSq d H M N f` (the *mean square* of the
cube mass `boxMass d (symIcc N) f n` over the slot box `massBox d H M = [±2HM]^d`), the
`(d+1)`-fold box-norm power of `f` at the window `arithIcc 1 (4HM+1)` is at least a constant times
`θ ^ 2`.

## The proof

Write `X n = boxMass d (symIcc N) f n = |S|⁻¹ cubeMassRaw d f n`, `L = 4HM+1`, `σ = |symIcc N|`,
and, for the cube terms `g_w = aN d f w` (`w : Fin d → ℤ`), let

`A w = ∑'_z ‖∑_{v ∈ arithIcc 1 L} g_w (z + v)‖²`

be the mass of the Fejér slots of `g_w`.  Three facts, all proved elsewhere in the tree, do the
work (this module only assembles them).

* **The fold** (`boxNormPow_ge_fold`, `cubeMass.Fold.lean`): the `(d+1)`-fold box-norm power at the
  window `Q = arithIcc 1 L` dominates `boxConst · Re ∑_{h,h'} Wf (d+1) f (h - h')`.
* **The fibre identity** (`cubeMass.fiberSum`) and the split in the first coordinate
  (`cubeMass.sumTdirCons`, `Wt_cons`, `aN_cons`) rewrite that pair sum as
  `∑_{w ∈ Tdir L d} Wt w ∑_δ Ncard L δ · (∑'_x g_w x · conj (g_w (x+δ)))`, and the Fejér identity
  (`cubeMass.fejerId`) turns the inner sum into `A w`; so
  `L^{2(d+1)} σ · boxNormPow (d+1) Q (symIcc N) f ≥ ∑_{w ∈ Tdir L d} Wt w · A w`.
* **The Fejér/Cauchy–Schwarz inequality** (`cubeMass.fejerCS`) bounds, for `w ∈ massBox`,
  `L² ‖∑'_x g_w x‖² ≤ (σ + L) · A w`, while `Wt w ≥ (L/2)^d` on the slot box
  (`Fintype.mem_piFinset` + `Ncard`).  Summing over `w ∈ massBox ⊆ Tdir L d` and using
  `∑_{w ∈ massBox} ‖boxMass‖² = L^d · massSq` gives

  `σ · massSq d H M N f ≤ 2^d (σ + L) · boxNormPow (d+1) Q (symIcc N) f`.

Finally, only the slot values with all coordinates in `[-2N,2N]` survive
(`cubeMassRaw_eq_zero`), so `massSq ≤ min (4N+1) L / L ≤ 4σ/(σ+L)`
(`cubeMass.massSq_le` + arithmetic).  Multiplying the two bounds gives
`(massSq)² ≤ 2^{d+2} · boxNormPow (d+1) Q (symIcc N) f`, which is the statement with
`s' = d+1`, `e = 2` and `C = 2^{-(d+2)}`.
-/

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse

/-! ## Elementary helpers -/

/-- `#(symIcc N) = 2N+1`. -/
lemma card_symIcc_eq (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The modulus of the normalised cube mass. -/
lemma norm_boxMass_eq (d : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) (n : Fin d → ℤ) :
    ‖boxMass d S f n‖ = ((S.card : ℝ))⁻¹ * ‖cubeMassRaw d f n‖ := by
  rw [boxMass_eq, norm_mul, norm_inv, Complex.norm_natCast]

/-- `z ∉ symIcc N` when `N < |z|`. -/
lemma not_mem_symIcc_of_lt {N : ℕ} {z : ℤ} (hz : N < z.natAbs) : z ∉ symIcc N :=
  fun h => absurd (natAbs_le_of_mem_symIcc h) (not_le.mpr hz)

/-- The mean square of the cube mass is non-negative. -/
lemma massSq_nonneg (d H M N : ℕ) (f : ℤ → ℂ) : 0 ≤ massSq d H M N f := by
  rw [massSq]
  exact div_nonneg (Finset.sum_nonneg (fun n _ => by positivity)) (by positivity)

/-- The slot box `massBox d H M` is contained in the difference box `Tdir (4HM+1) d`. -/
lemma massBox_subset_Tdir (d H M : ℕ) : massBox d H M ⊆ Tdir (massBoxCard H M) d := by
  intro w hw
  rw [mem_Tdir]
  intro i
  rw [mem_sCard]
  have h := (Fintype.mem_piFinset.mp hw) i
  rw [Finset.mem_Icc] at h
  have h1 : (w i : ℤ) ≤ 2 * ((H * M : ℕ) : ℤ) := by
    have := h.2; unfold massHalf at this; exact this
  have h2 : -(2 * ((H * M : ℕ) : ℤ)) ≤ (w i : ℤ) := by
    have := h.1; unfold massHalf at this; exact this
  have hL : ((massBoxCard H M : ℕ) : ℤ) = 4 * ((H * M : ℕ) : ℤ) + 1 := by
    unfold massBoxCard; push_cast; ring
  rw [hL]
  omega

/-- On the slot box the multiplicity `Wt (4HM+1) d w` of a difference dominates `(L/2)^d`. -/
lemma Wt_lower_massBox {d H M : ℕ} {w : Fin d → ℤ} (hw : w ∈ massBox d H M) :
    ((massBoxCard H M : ℝ) / 2) ^ d ≤ (Wt (massBoxCard H M) d w : ℝ) := by
  have h2 : ∀ i : Fin d, 2 * (H * M) + 1 ≤ Ncard (massBoxCard H M) (w i) := by
    intro i
    have h := (Fintype.mem_piFinset.mp hw) i
    rw [Finset.mem_Icc] at h
    have h1 : (w i : ℤ) ≤ (((2 * (H * M) : ℕ)) : ℤ) := by
      have := h.2; unfold massHalf at this; push_cast at this ⊢; linarith
    have h2' : -(((2 * (H * M) : ℕ)) : ℤ) ≤ (w i : ℤ) := by
      have := h.1; unfold massHalf at this; push_cast at this ⊢; linarith
    have habs : (w i).natAbs ≤ 2 * (H * M) := by
      have hZ : (((w i).natAbs : ℕ) : ℤ) ≤ (((2 * (H * M) : ℕ)) : ℤ) := by
        rw [Int.natCast_natAbs]
        exact abs_le.mpr ⟨h2', h1⟩
      exact_mod_cast hZ
    rw [show Ncard (massBoxCard H M) (w i) = massBoxCard H M - (w i).natAbs from rfl]
    unfold massBoxCard
    rw [show 4 * H * M = 4 * (H * M) from by ring,
      show 2 * (H * M) + 1 = 4 * (H * M) + 1 - 2 * (H * M) from by omega]
    exact Nat.sub_le_sub_left habs (4 * (H * M) + 1)
  have hprod : ∏ i : Fin d, (2 * (H * M) + 1) ≤ Wt (massBoxCard H M) d w := by
    rw [Wt]
    exact Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => h2 i)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hmain : (((2 * (H * M) + 1 : ℕ)) : ℝ) ^ d ≤ (Wt (massBoxCard H M) d w : ℝ) := by
    exact_mod_cast hprod
  refine le_trans (pow_le_pow_left₀ (by positivity) ?_ d) hmain
  have hcast : ((massBoxCard H M : ℝ)) = 4 * (H : ℝ) * (M : ℝ) + 1 := by
    unfold massBoxCard; push_cast; ring
  rw [hcast]
  push_cast
  linarith

/-! ## The fold: the pair sum over the difference window -/

section FoldLocal

/-- `boxConstC` has the modulus `boxConst`. -/
private theorem norm_boxConstC_local (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) :
    ‖boxConstC t Q S‖ = boxConst t Q S := by
  unfold boxConstC boxConst
  have h : ∀ i : Fin t, ‖(((Q i).card : ℂ))⁻¹‖ = (((Q i).card : ℝ))⁻¹ :=
    fun i => by rw [norm_inv, Complex.norm_natCast]
  simp only [norm_mul, norm_inv, Complex.norm_natCast, norm_prod, h]

/-- `boxConst` is non-negative. -/
private theorem boxConst_nonneg (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) :
    0 ≤ boxConst t Q S := by
  unfold boxConst
  positivity

/-- The multiplicity of a difference splits in the first coordinate. -/
private theorem Wt_cons_local (Card d : ℕ) (δ : ℤ) (n : Fin d → ℤ) :
    Wt Card (d + 1) (Fin.cons δ n) = Ncard Card δ * Wt Card d n := by
  rw [Wt, Wt, Fin.prod_univ_succ]
  rfl

/-- **The pair-sum lower bound for the box-norm power.**  For `1 ≤ t`, a direction family `Q`, a
window `S` and a finitely supported `f`,

`(|S| ∏_i |Q i|²)⁻¹ · Re ∑_{h,h' ∈ ∏ Q} Wf t f (h - h') ≤ ‖f‖^{2^t}_{□^t_Q(S)}`. -/
private theorem boxNormPow_ge_fold_local (t : ℕ) (ht : 1 ≤ t) (Q : Fin t → Finset ℤ)
    (S : Finset ℤ) {f : ℤ → ℂ} (hf : FinSuppZ f) :
    boxConst t Q S
      * (∑ h : (i : Fin t) → ↥(Q i), ∑ h' : (i : Fin t) → ↥(Q i),
          Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f)
            (fun i => (h i : ℤ) - (h' i : ℤ))).re
      ≤ boxNormPow t Q S f := by
  classical
  set Z : ℂ := ∑ h : (i : Fin t) → ↥(Q i), ∑ h' : (i : Fin t) → ↥(Q i),
      Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f) (fun i => (h i : ℤ) - (h' i : ℤ))
    with hZdef
  have hZ : Work.Peluse.boxSumPow t Q S f = boxConstC t Q S * Z := by
    have hfold := Work.Peluse.PET.prodCubeSum_fold_gen (t := t) Q S
      (F := fun _ : Fin t → Bool => f)
      (fun h h' => Work.Peluse.Concat.tsum_cube_corner_eq_shrink _ h h')
    unfold Work.Peluse.boxSumPow boxConstC
    rw [hZdef]
    exact hfold
  have h1 : boxNormPow t Q S f = boxConst t Q S * ‖Z‖ := by
    have h2 := congrArg (fun z : ℂ => ‖z‖) hZ
    rw [norm_mul, norm_boxConstC_local] at h2
    exact h2
  rw [h1]
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm Z) (boxConst_nonneg t Q S)

end FoldLocal

/-- **The folded pair sum.**  The double sum of the reduced cube terms over pairs of tuples in
`(arithIcc 1 L)^{d+1}` equals the sum over the difference box `Tdir L d` of the multiplicity
`Wt L d w` times the Fejér mass `A w = ∑'_z ‖∑_{v ∈ arithIcc 1 L} aN d f w (z+v)‖²` — the
composition of the fibre identity (`cubeMass.fiberSum`), the split of the multiplicity in the first
coordinate (`cubeMass.sumTdirCons`, `Wt_cons`), the split of the cube term (`aN_cons`) and the Fejér
identity (`cubeMass.fejerId`). -/
theorem foldedSum_eq (d L : ℕ) (hL : 1 ≤ L) (f : ℤ → ℂ) (hf : FinSuppZ f) :
    (∑ h : (i : Fin (d+1)) → ↥(arithIcc 1 L), ∑ h' : (i : Fin (d+1)) → ↥(arithIcc 1 L),
        Concat.Wf (d+1) (fun _ : Fin (d+1) → Bool => f) (fun i => (h i : ℤ) - (h' i : ℤ)))
      = ((∑ w ∈ Tdir L d, (Wt L d w : ℝ) *
            ∑' z : ℤ, ‖∑ v ∈ arithIcc 1 L, aN d f w (z + v)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  obtain ⟨N, hN⟩ := hf
  -- the cube terms are finitely supported
  have hfin : ∀ w : Fin d → ℤ, FinSuppZ (aN d f w) := by
    intro w
    exact ⟨N, fun z hz => aN_eq_zero_of_notMem_symIcc hN w (not_mem_symIcc_of_lt hz)⟩
  -- the reduced cube term is the un-normalised cube mass
  have hWf : ∀ u : Fin (d+1) → ℤ,
      Concat.Wf (d+1) (fun _ : Fin (d+1) → Bool => f) u = cubeMassRaw (d+1) f u := by
    intro u
    rw [Wf_const]
    rfl
  -- the fibre identity
  rw [cubeMass.fiberSum (Card := L) (t := d + 1) hL
    (fun u => Concat.Wf (d+1) (fun _ : Fin (d+1) → Bool => f) u)]
  have h1 : ∀ u ∈ Tdir L (d + 1),
      (((Wt L (d + 1) u : ℕ) : ℂ) * Concat.Wf (d + 1) (fun _ : Fin (d + 1) → Bool => f) u)
        = ((Wt L (d + 1) u : ℕ) : ℂ) * cubeMassRaw (d + 1) f u := by
    intro u _
    rw [hWf u]
  rw [Finset.sum_congr rfl h1]
  rw [cubeMass.sumTdirCons]
  -- split each summand
  have hstep : ∀ δ ∈ sCard L, ∀ w ∈ Tdir L d,
      (((Wt L (d + 1) (Fin.cons δ w) : ℕ) : ℂ) * cubeMassRaw (d + 1) f (Fin.cons δ w))
        = ((Ncard L δ : ℕ) : ℂ) * ((Wt L d w : ℕ) : ℂ) *
            (∑' x : ℤ, aN d f w x * star (aN d f w (x + δ))) := by
    intro δ hδ w hw
    have hcm : cubeMassRaw (d + 1) f (Fin.cons δ w)
        = ∑' x : ℤ, aN d f w x * star (aN d f w (x + δ)) := by
      simp only [cubeMassRaw, aN]
      exact tsum_congr (fun x => aN_cons f w δ x)
    rw [hcm, Wt_cons_local]
    push_cast
    ring
  refine Eq.trans (Finset.sum_congr rfl (fun δ hδ => Finset.sum_congr rfl (fun w hw => hstep δ hδ w hw))) ?_
  -- exchange the two sums and apply the Fejér identity
  rw [Finset.sum_comm]
  have hstep2 : ∀ w ∈ Tdir L d,
      (∑ δ ∈ sCard L, ((Ncard L δ : ℕ) : ℂ) * ((Wt L d w : ℕ) : ℂ) *
          (∑' x : ℤ, aN d f w x * star (aN d f w (x + δ))))
        = ((Wt L d w : ℕ) : ℂ) *
            ((∑' z : ℤ, ‖∑ v ∈ arithIcc 1 L, aN d f w (z + v)‖ ^ 2 : ℝ) : ℂ) := by
    intro w hw
    rw [← cubeMass.fejerId L hL (aN d f w) (hfin w)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun δ _ => by ring)
  rw [Finset.sum_congr rfl hstep2]
  have hfin2 : ∀ w ∈ Tdir L d, (((Wt L d w : ℕ) : ℂ) *
        ((∑' z : ℤ, ‖∑ v ∈ arithIcc 1 L, aN d f w (z + v)‖ ^ 2 : ℝ) : ℂ))
      = ((((Wt L d w : ℝ)) * (∑' z : ℤ, ‖∑ v ∈ arithIcc 1 L, aN d f w (z + v)‖ ^ 2) : ℝ) : ℂ) := by
    intro w _
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  rw [Finset.sum_congr rfl hfin2, ← Complex.ofReal_sum]

/-! ## The two numeric bounds -/

/-- **The slot-box ratio bound**: `massSq ≤ 4σ/(σ+L)` with `σ = |symIcc N|`, `L = 4HM+1`.  This is
`cubeMass.massSq_le` (`massSq ≤ min (4N+1) L / L`, since only the slot values with all coordinates in
`[-2N,2N]` have a non-vanishing cube mass) plus the arithmetic
`min (4N+1) L / L ≤ 4(2N+1)/(2N+1+L)`. -/
theorem massSq_ratio {d H M N : ℕ} (hd : 1 ≤ d) {f : ℤ → ℂ}
    (hsup : SupportIn f N) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    massSq d H M N f ≤ 4 * ((symIcc N).card : ℝ) /
      (((symIcc N).card : ℝ) + (massBoxCard H M : ℝ)) := by
  have h := cubeMass.massSq_le d H M N hd f hsup hbd
  rw [card_symIcc_eq]
  have hLpos : (0 : ℝ) < ((massBoxCard H M : ℕ) : ℝ) := by
    have h0 : 0 < massBoxCard H M := by unfold massBoxCard; omega
    exact_mod_cast h0
  have hden : (0 : ℝ) < (((2 * N + 1 : ℕ)) : ℝ) + ((massBoxCard H M : ℕ) : ℝ) := by positivity
  refine le_trans h ?_
  have hcr : ((min (4 * N + 1) (massBoxCard H M) : ℕ) : ℝ) *
      (((2 * N + 1 : ℕ) : ℝ) + ((massBoxCard H M : ℕ) : ℝ)) ≤
      4 * (((2 * N + 1 : ℕ)) : ℝ) * ((massBoxCard H M : ℕ) : ℝ) := by
    rcases le_total (massBoxCard H M) (4 * N + 1) with hc | hc
    · rw [min_eq_right hc]
      have hc' : ((massBoxCard H M : ℕ) : ℝ) ≤ 4 * (N : ℝ) + 1 := by
        have hcast : (((4 * N + 1 : ℕ)) : ℝ) = 4 * (N : ℝ) + 1 := by push_cast; ring
        calc ((massBoxCard H M : ℕ) : ℝ) ≤ (((4 * N + 1 : ℕ)) : ℝ) := by exact_mod_cast hc
          _ = 4 * (N : ℝ) + 1 := hcast
      push_cast
      nlinarith [hLpos, hc', (show (0 : ℝ) ≤ (N : ℝ) by positivity)]
    · rw [min_eq_left hc]
      have hc' : 4 * (N : ℝ) + 1 ≤ ((massBoxCard H M : ℕ) : ℝ) := by
        have hcast : (((4 * N + 1 : ℕ)) : ℝ) = 4 * (N : ℝ) + 1 := by push_cast; ring
        calc 4 * (N : ℝ) + 1 = (((4 * N + 1 : ℕ)) : ℝ) := hcast.symm
          _ ≤ ((massBoxCard H M : ℕ) : ℝ) := by exact_mod_cast hc
      push_cast
      nlinarith [hLpos, hc', (show (0 : ℝ) ≤ (N : ℝ) by positivity)]
  have hrew : ((min (4 * N + 1) (massBoxCard H M) : ℕ) : ℝ) / ((massBoxCard H M : ℕ) : ℝ) ≤
      4 * (((2 * N + 1 : ℕ)) : ℝ) / ((((2 * N + 1 : ℕ)) : ℝ) + ((massBoxCard H M : ℕ) : ℝ)) ↔
      ((min (4 * N + 1) (massBoxCard H M) : ℕ) : ℝ) *
          ((((2 * N + 1 : ℕ)) : ℝ) + ((massBoxCard H M : ℕ) : ℝ))
        ≤ 4 * (((2 * N + 1 : ℕ)) : ℝ) * ((massBoxCard H M : ℕ) : ℝ) := by
    rw [le_div_iff₀ hden, div_mul_eq_mul_div, div_le_iff₀ hLpos]
  exact hrew.mpr hcr

/-- **The main inequality**: `σ · massSq ≤ 2^d (σ+L) · boxNormPow (d+1) Q (symIcc N) f`. -/
theorem massSq_mul_card_le {d H M N : ℕ} (hd : 1 ≤ d) {f : ℤ → ℂ} (hsup : SupportIn f N) :
    ((symIcc N).card : ℝ) * massSq d H M N f
      ≤ (2 : ℝ) ^ d * (((symIcc N).card : ℝ) + (massBoxCard H M : ℝ)) *
        boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 (massBoxCard H M))
          (symIcc N) f := by
  classical
  set L : ℕ := massBoxCard H M with hL
  set σ : ℕ := (symIcc N).card with hσ
  have hL1 : 1 ≤ L := by rw [hL]; unfold massBoxCard; omega
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  have hσpos : (0 : ℝ) < (σ : ℝ) := by
    rw [hσ, card_symIcc_eq]; positivity
  have hfZ : FinSuppZ f := ⟨N, hsup⟩
  set A : (Fin d → ℤ) → ℝ := fun w => ∑' z : ℤ, ‖∑ v ∈ arithIcc 1 L, aN d f w (z + v)‖ ^ 2 with hA
  have hAnn : ∀ w, 0 ≤ A w := fun w => tsum_nonneg (fun z => by positivity)
  -- Step 1: the fold
  have hge := boxNormPow_ge_fold_local (t := d + 1) (by omega)
    (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N) hfZ
  rw [foldedSum_eq d L hL1 f hfZ] at hge
  simp only [Complex.ofReal_re] at hge
  have hbc : boxConst (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N)
      = (σ : ℝ)⁻¹ * (((L : ℝ) ^ (2 * (d + 1))))⁻¹ := by
    unfold boxConst
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Concat.card_arithIcc_shrink one_ne_zero L, hσ, mul_assoc, ← pow_add, inv_pow,
      show (d + 1) + (d + 1) = 2 * (d + 1) from by omega]
  rw [hbc] at hge
  -- hence the weighted sum of the Fejér masses is bounded
  have hS2 : (∑ w ∈ Tdir L d, (Wt L d w : ℝ) * A w)
      ≤ (σ : ℝ) * (L : ℝ) ^ (2 * (d + 1)) *
          boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N) f := by
    have hmul := mul_le_mul_of_nonneg_left hge
      (show (0 : ℝ) ≤ (σ : ℝ) * (L : ℝ) ^ (2 * (d + 1)) by positivity)
    have hid : (σ : ℝ) * (L : ℝ) ^ (2 * (d + 1)) *
        ((σ : ℝ)⁻¹ * (((L : ℝ) ^ (2 * (d + 1))))⁻¹ *
          ∑ w ∈ Tdir L d, (Wt L d w : ℝ) * A w)
        = ∑ w ∈ Tdir L d, (Wt L d w : ℝ) * A w := by
      field_simp
      try ring
    rwa [hid] at hmul
  -- Step 2: `σ * massSq` as a sum of cube-mass squares
  have hmass_eq : (σ : ℝ) * massSq d H M N f
      = (σ : ℝ)⁻¹ * (((L : ℝ)) ^ d)⁻¹ * ∑ w ∈ massBox d H M, ‖cubeMassRaw d f w‖ ^ 2 := by
    have hcard : massBoxCard H M = L := hL.symm
    rw [massSq, hcard]
    have hnorm : ∀ w : Fin d → ℤ,
        ‖boxMass d (symIcc N) f w‖ = (σ : ℝ)⁻¹ * ‖cubeMassRaw d f w‖ := by
      intro w
      rw [norm_boxMass_eq, ← hσ]
    simp only [hnorm]
    rw [div_eq_mul_inv]
    have h1 : ∑ w ∈ massBox d H M, ((σ : ℝ)⁻¹ * ‖cubeMassRaw d f w‖) ^ 2
        = (σ : ℝ)⁻¹ ^ 2 * ∑ w ∈ massBox d H M, ‖cubeMassRaw d f w‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [h1]
    field_simp
    try ring
  -- Step 3: the Fejér/Cauchy–Schwarz bound of each slot value
  have hterm : ∀ w ∈ massBox d H M,
      (L : ℝ) ^ 2 * ‖cubeMassRaw d f w‖ ^ 2 ≤ ((σ : ℝ) + L) * A w := by
    intro w hw
    have hsuppw : SupportIn (aN d f w) N := fun z hz =>
      aN_eq_zero_of_notMem_symIcc hsup w (not_mem_symIcc_of_lt hz)
    have hcs := cubeMass.fejerCS L hL1 hsuppw
    have hσeq : ((symIcc N).card : ℝ) = (σ : ℝ) := by rw [hσ]
    rw [hσeq] at hcs
    have hcr : cubeMassRaw d f w = ∑' x : ℤ, aN d f w x := by
      simp only [cubeMassRaw, aN]
    rw [hcr]
    exact hcs
  -- Step 4: the multiplicity bound on the slot box
  have hwt : ∀ w ∈ massBox d H M,
      A w ≤ (2 : ℝ) ^ d * (((L : ℝ)) ^ d)⁻¹ * ((Wt L d w : ℝ) * A w) := by
    intro w hw
    have hlow := Wt_lower_massBox (d := d) (H := H) (M := M) (w := w) hw
    rw [← hL] at hlow
    rw [div_pow] at hlow
    have h2 : (L : ℝ) ^ d / (2 : ℝ) ^ d * A w ≤ (Wt L d w : ℝ) * A w :=
      mul_le_mul_of_nonneg_right hlow (hAnn w)
    have hc : (0 : ℝ) < (L : ℝ) ^ d / (2 : ℝ) ^ d := by positivity
    have h3 : A w ≤ ((L : ℝ) ^ d / (2 : ℝ) ^ d)⁻¹ * ((Wt L d w : ℝ) * A w) := by
      have h4 := mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hc))
      rwa [inv_mul_cancel_left₀ hc.ne'] at h4
    have h5 : ((L : ℝ) ^ d / (2 : ℝ) ^ d)⁻¹ = (2 : ℝ) ^ d * (((L : ℝ)) ^ d)⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    rwa [h5] at h3
  -- Step 5: assemble
  have hsum1 : (∑ w ∈ massBox d H M, (L : ℝ) ^ 2 * ‖cubeMassRaw d f w‖ ^ 2)
      ≤ ((σ : ℝ) + L) * ∑ w ∈ massBox d H M, A w := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hS1 : (∑ w ∈ massBox d H M, ‖cubeMassRaw d f w‖ ^ 2)
      ≤ ((L : ℝ) ^ 2)⁻¹ * ((σ : ℝ) + L) * (∑ w ∈ massBox d H M, A w) := by
    have h4 := mul_le_mul_of_nonneg_left hsum1 (show (0 : ℝ) ≤ ((L : ℝ) ^ 2)⁻¹ by positivity)
    have hid : ((L : ℝ) ^ 2)⁻¹ * (∑ w ∈ massBox d H M, (L : ℝ) ^ 2 * ‖cubeMassRaw d f w‖ ^ 2)
        = ∑ w ∈ massBox d H M, ‖cubeMassRaw d f w‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      field_simp
    rw [hid] at h4
    simpa only [mul_assoc] using h4
  have hsum2 : (∑ w ∈ massBox d H M, A w)
      ≤ (2 : ℝ) ^ d * (((L : ℝ)) ^ d)⁻¹ *
          (∑ w ∈ Tdir L d, (Wt L d w : ℝ) * A w) := by
    calc (∑ w ∈ massBox d H M, A w)
        ≤ ∑ w ∈ massBox d H M, (2 : ℝ) ^ d * (((L : ℝ)) ^ d)⁻¹ * ((Wt L d w : ℝ) * A w) :=
          Finset.sum_le_sum hwt
      _ = (2 : ℝ) ^ d * (((L : ℝ)) ^ d)⁻¹ *
            ∑ w ∈ massBox d H M, ((Wt L d w : ℝ) * A w) := by
          rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ d * (((L : ℝ)) ^ d)⁻¹ *
            ∑ w ∈ Tdir L d, ((Wt L d w : ℝ) * A w) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (massBox_subset_Tdir d H M)
            (fun w _ _ => by positivity)
  have hpow2 : (L : ℝ) ^ (2 * (d + 1)) = (L : ℝ) ^ d * (L : ℝ) ^ d * (L : ℝ) ^ 2 := by
    rw [show 2 * (d + 1) = d + d + 2 by ring, pow_add, pow_add]
  have hfin : (σ : ℝ) * massSq d H M N f ≤ (2 : ℝ) ^ d * ((σ : ℝ) + L) *
      boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N) f := by
    rw [hmass_eq]
    calc (σ : ℝ)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (∑ w ∈ massBox d H M, ‖cubeMassRaw d f w‖ ^ 2)
        ≤ (σ : ℝ)⁻¹ * ((L : ℝ) ^ d)⁻¹ *
            (((L : ℝ) ^ 2)⁻¹ * ((σ : ℝ) + L) * (∑ w ∈ massBox d H M, A w)) :=
          mul_le_mul_of_nonneg_left hS1 (by positivity)
      _ ≤ (σ : ℝ)⁻¹ * ((L : ℝ) ^ d)⁻¹ *
            (((L : ℝ) ^ 2)⁻¹ * ((σ : ℝ) + L) *
              ((2 : ℝ) ^ d * ((L : ℝ) ^ d)⁻¹ *
                (∑ w ∈ Tdir L d, (Wt L d w : ℝ) * A w))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsum2 (by positivity)) (by positivity)
      _ ≤ (σ : ℝ)⁻¹ * ((L : ℝ) ^ d)⁻¹ *
            (((L : ℝ) ^ 2)⁻¹ * ((σ : ℝ) + L) *
              ((2 : ℝ) ^ d * ((L : ℝ) ^ d)⁻¹ *
                ((σ : ℝ) * (L : ℝ) ^ (2 * (d + 1)) *
                  boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N) f))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hS2 (by positivity)) (by positivity)) (by positivity)
      _ = (2 : ℝ) ^ d * ((σ : ℝ) + L) *
            boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N) f := by
          rw [hpow2]
          field_simp
          try ring
  exact hfin

/-- **The mean square of the cube mass controls the box-norm power.** -/
theorem massSq_sq_le {d H M N : ℕ} (hd : 1 ≤ d) {f : ℤ → ℂ}
    (hsup : SupportIn f N) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    (massSq d H M N f) ^ 2 ≤ (2 : ℝ) ^ (d + 2) *
      boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 (massBoxCard H M)) (symIcc N) f := by
  set L : ℕ := massBoxCard H M with hL
  set σ : ℕ := (symIcc N).card with hσ
  have hA : massSq d H M N f ≤ 4 * (σ : ℝ) / ((σ : ℝ) + (L : ℝ)) := by
    have h := massSq_ratio (d := d) (H := H) (M := M) (N := N) hd hsup hbd
    rwa [← hL, ← hσ] at h
  have hB := massSq_mul_card_le (d := d) (H := H) (M := M) (N := N) hd hsup
  rw [← hL, ← hσ] at hB
  have hMnn : 0 ≤ massSq d H M N f := massSq_nonneg d H M N f
  have hden : (0 : ℝ) < (σ : ℝ) + (L : ℝ) := by
    have : (0 : ℝ) < (σ : ℝ) := by rw [hσ, card_symIcc_eq]; positivity
    linarith
  have h1 : (massSq d H M N f) ^ 2 ≤ massSq d H M N f * (4 * (σ : ℝ) / ((σ : ℝ) + (L : ℝ))) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hA hMnn
  have h2 : massSq d H M N f * (4 * (σ : ℝ) / ((σ : ℝ) + (L : ℝ))) ≤ 4 * (2 : ℝ) ^ d *
      boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N) f := by
    have hid : massSq d H M N f * (4 * (σ : ℝ) / ((σ : ℝ) + (L : ℝ)))
        = (4 / ((σ : ℝ) + (L : ℝ))) * ((σ : ℝ) * massSq d H M N f) := by
      field_simp
      try ring
    rw [hid]
    have h4 : (4 / ((σ : ℝ) + (L : ℝ))) * ((σ : ℝ) * massSq d H M N f)
        ≤ (4 / ((σ : ℝ) + (L : ℝ))) *
            ((2 : ℝ) ^ d * ((σ : ℝ) + (L : ℝ)) *
              boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N) f) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    have h5 : (4 / ((σ : ℝ) + (L : ℝ))) *
          ((2 : ℝ) ^ d * ((σ : ℝ) + (L : ℝ)) *
            boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N) f)
        = 4 * (2 : ℝ) ^ d *
            boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 L) (symIcc N) f := by
      field_simp
      try ring
    linarith [h4, h5.le, h5.ge]
  have h32 : (2 : ℝ) ^ (d + 2) = 4 * (2 : ℝ) ^ d := by
    rw [pow_add]; ring
  calc (massSq d H M N f) ^ 2 ≤ 4 * (2 : ℝ) ^ d *
        boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 (massBoxCard H M)) (symIcc N) f :=
        le_trans h1 h2
    _ = (2 : ℝ) ^ (d + 2) *
        boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 (massBoxCard H M)) (symIcc N) f := by
        rw [h32]

/-- **`SqToCube`** — the *mean square* of the cube mass over the slot box controls the box-norm
power at the slot window (KKL, arXiv:2407.08636, §8, the passage from (57) to the end of the proof
of Theorem 1.10; the `d`-fold case of the Fejér conversion, with the Cauchy–Schwarz step already
performed — `SwapE/Reduce.lean`'s `massToCube_of_sq : SqToCube → MassToCube` recovers the
`massAvg` form from this one using only `massAvg_sq_le`).

Writing `X n = boxMass d (symIcc N) f n = |S|⁻¹ ∑_x ∏_{ω : Fin d → Bool} C^{|ω|} f (x + ω·n)`
(the `2^d`-fold cube term along the directions `n`), the hypothesis is
`θ ≤ massSq d H M N f = (∑_{n ∈ massBox} ‖X n‖²) / (4HM+1)^d` with `massBox = [-2HM, 2HM]^d`, and
the conclusion is a lower bound for the `s'`-fold box-norm power of `f` at the window
`arithIcc 1 (4HM+1)`.

The proof (`massSq_sq_le`, `s' = d + 1`, `e = 2`, `C = 2^{-(d+2)}`) is the fold of the
`(d+1)`-fold box form into the Fejér slots of the cube terms `aN d f w` (`foldedSum_eq`), the
Fejér/Cauchy–Schwarz inequality of each slot (`cubeMass.fejerCS`), the multiplicity bound
`Wt w ≥ (L/2)^d` on the slot box and the support bound `massSq ≤ 4σ/(σ+L)`
(`cubeMass.massSq_le`). -/
theorem sqToCube : Work.Peluse.SwapE.SqToCube := by
  intro d hd
  refine ⟨2, by norm_num, d + 1, by omega, ((2 : ℝ) ^ (d + 2))⁻¹, by positivity, ?_⟩
  intro H M N θ f hH hM hf hf1 hθ hmass
  have hmain := massSq_sq_le (d := d) (H := H) (M := M) (N := N) hd hf hf1
  have hθ2 : θ ^ 2 ≤ (massSq d H M N f) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul hmass hmass hθ.le (massSq_nonneg d H M N f)
  have hfin : ((2 : ℝ) ^ (d + 2))⁻¹ * θ ^ 2 ≤
      boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 (massBoxCard H M))
        (symIcc N) f := by
    have hpow : ((2 : ℝ) ^ (d + 2))⁻¹ * (2 : ℝ) ^ (d + 2) = 1 :=
      inv_mul_cancel₀ (by positivity)
    have h1 : ((2 : ℝ) ^ (d + 2))⁻¹ * θ ^ 2 ≤
        ((2 : ℝ) ^ (d + 2))⁻¹ * ((2 : ℝ) ^ (d + 2) *
          boxNormPow (d + 1) (fun _ : Fin (d + 1) => arithIcc 1 (massBoxCard H M))
            (symIcc N) f) :=
      mul_le_mul_of_nonneg_left (le_trans hθ2 hmain) (by positivity)
    rwa [← mul_assoc, hpow, one_mul] at h1
  exact hfin

end

end Work.Peluse.SwapE
