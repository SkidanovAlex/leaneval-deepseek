import Mathlib
import Submission.Work.Peluse.Peel.boxSumPow_peel
import Submission.Work.Peluse.Peel.boxNormPow_one_tsum
import Submission.Work.Peluse.LevelRaise.boxNormPow_succ_ge
import Submission.Work.Peluse.Concat.arithIcc_shrink_dvd_ge

/-!
# Scale transfer for Peluse's box norms over arithmetic progressions

The target of this file is `Work.Peluse.PET.boxNormPow_scale_transfer`: for every `k ≥ 1` there
are constants `c > 0` and `e ≥ 0` such that for every non-zero direction tuple `d : Fin k → ℤ`,
every `1 ≤ H' ≤ H` with `H' ∣ H`, every window `S` and every finitely supported `f`,

`c * (H'/H)^e * ‖f‖^{2^k}_{□^k_{d_1[H],…,d_k[H]}(S)} ≤ ‖f‖^{2^k}_{□^k_{d_1[H'],…,d_k[H']}(S)}`.

The proof gives the sharp form `c = 1`, `e = 0`: the box-norm power is *decreasing* in the length
of the arithmetic progressions, for lengths related by divisibility.

The mechanism is the one used for the already-proved constant-direction case
(`Work.Peluse.Concat.arithIcc_shrink_dvd_ge`): writing `H = B · H'`, the blocks
`d_i[H'] + H'·d_i·j`, `j < B`, decompose `d_i[H]`, so the level-`k` box sum over the long
directions is a sum of `B^{2k}` copies of the level-`k` box sum over the short directions
(up to shifts of `f`, which the box norm does not see, `Work.Peluse.BoxNorm.boxNormPow_shift`),
each of which is bounded by the Gowers–Cauchy–Schwarz inequality
(`Work.Peluse.BoxNorm.prodCubeSum_norm_le`).  The `B^{2k}` terms exactly cancel against the
cardinality ratio `(∏_i |d_i[H]|/|d_i[H']|)^{-2} = B^{-2k}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.PET

noncomputable section

open Work.Peluse

/-! ## Folding `prodCubeSum` for an arbitrary direction family -/

/-- **Folding the cube sum.**  For an arbitrary direction family `Q` the cube sum of `2^t` (not
necessarily equal) functions is its normalising constant times the sum, over the pairs of shift
tuples in `∏_i Q_i`, of the reduced cube term `Wf` evaluated at the *difference* of the two tuples.
The one input is the elementary reindexing of the `x`-sum
(`Work.Peluse.Concat.tsum_cube_corner_eq_shrink`), supplied as the hypothesis `hc`. -/
theorem prodCubeSum_fold_gen {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    {F : (Fin t → Bool) → ℤ → ℂ}
    (hc : ∀ (h h' : Fin t → ℤ),
      (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F ω (x + Work.Peluse.cornerShift h h' ω)))
        = ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (F ω (x + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω))) :
    Work.Peluse.prodCubeSum t Q S F
      = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹)
          * ∑ h : (i : Fin t) → ↥(Q i), ∑ h' : (i : Fin t) → ↥(Q i),
              Work.Peluse.Concat.Wf t F (fun i => (h i : ℤ) - (h' i : ℤ)) := by
  rw [Work.Peluse.prodCubeSum_eq]
  refine congrArg (fun z => ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹)
      * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * z) ?_
  refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
  exact hc (fun i => (h i : ℤ)) (fun i => (h' i : ℤ))

/-- **Folding the cube sum of a shifted family.**  The same fold for the family
`ω ↦ T_{cornerShift e 0 ω} (F ω)`: the extra corner shift is absorbed into the argument of `F`, so
the reduced cube term is evaluated at `(r - r') + e`. -/
theorem prodCubeSum_shiftFam_gen {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    {F : (Fin t → Bool) → ℤ → ℂ} (e : Fin t → ℤ)
    (hc : ∀ (G : (Fin t → Bool) → ℤ → ℂ) (h h' : Fin t → ℤ),
      (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (G ω (x + Work.Peluse.cornerShift h h' ω)))
        = ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (G ω (x + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω))) :
    Work.Peluse.prodCubeSum t Q S
        (fun ω : Fin t → Bool => Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω))
      = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹)
          * ∑ r : (i : Fin t) → ↥(Q i), ∑ r' : (i : Fin t) → ↥(Q i),
              Work.Peluse.Concat.Wf t F ((fun i => (r i : ℤ) - (r' i : ℤ)) + e) := by
  rw [prodCubeSum_fold_gen
    (F := fun ω : Fin t → Bool => Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω)) Q S
    ((hc (fun ω : Fin t → Bool => Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω))))]
  refine congrArg (fun z => ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹)
      * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * z) ?_
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun r' _ => ?_))
  refine tsum_congr (fun x => ?_)
  refine Finset.prod_congr rfl (fun ω _ => ?_)
  rw [Work.Peluse.Concat.cornerShift_zero_add_shrink]
  have hshift : Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω)
        (x + Work.Peluse.cornerShift (fun i => (r i : ℤ) - (r' i : ℤ)) 0 ω)
      = F ω ((x + Work.Peluse.cornerShift (fun i => (r i : ℤ) - (r' i : ℤ)) 0 ω)
          + Work.Peluse.cornerShift e 0 ω) := rfl
  change star^[Work.Peluse.weight ω]
      (Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω)
        (x + Work.Peluse.cornerShift (fun i => (r i : ℤ) - (r' i : ℤ)) 0 ω))
    = star^[Work.Peluse.weight ω]
        (F ω (x + (Work.Peluse.cornerShift (fun i => (r i : ℤ) - (r' i : ℤ)) 0 ω
          + Work.Peluse.cornerShift e 0 ω)))
  rw [hshift]
  congr 1
  ring

/-! ## The block decomposition of the tuple sums -/

/-- **The block equivalence.**  For a non-zero direction tuple `d` and `H = B · H'`, the index set
`∀ i, ↥(d_i[H])` is the product of the residue index set `∀ i, ↥(d_i[H'])` and the block index set
`∀ i, Fin B`, with the coordinate description `(r, j) ↦ r i + d i · H' · (j i)`. -/
theorem arithIcc_blockEquiv_gen {t : ℕ} {d : Fin t → ℤ} (hd : ∀ i, d i ≠ 0) {B H' : ℕ}
    (hB : 1 ≤ B) (hH' : 1 ≤ H') :
    ∃ e : (∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B * H')))
            ≃ ((∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) H')) × (∀ i : Fin t, Fin B)),
      ∀ (r : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) H')) (j : ∀ i : Fin t, Fin B)
        (i : Fin t),
        ((e.symm (r, j)) i : ℤ) = (r i : ℤ) + d i * H' * (j i : ℤ) := by
  classical
  have hcoord : ∀ i : Fin t, ∃ ei : ↥(Work.Peluse.arithIcc (d i) (B * H'))
      ≃ (↥(Work.Peluse.arithIcc (d i) H') × Fin B),
      ∀ (r : ↥(Work.Peluse.arithIcc (d i) H')) (j : Fin B),
        ((ei.symm (r, j) : ↥(Work.Peluse.arithIcc (d i) (B * H'))) : ℤ)
          = (r : ℤ) + d i * H' * (j : ℤ) :=
    fun i => Work.Peluse.Concat.arithIcc_blockEquiv_shrink (c := d i) (hd i) (L' := H') (m := B)
      (L := B * H') rfl hH' hB
  choose ei hei using hcoord
  refine ⟨?_, ?_⟩
  · refine
      { toFun := fun h => (fun i => (ei i (h i)).1, fun i => (ei i (h i)).2)
        invFun := fun p => fun i => (ei i).symm (p.1 i, p.2 i)
        left_inv := ?_
        right_inv := ?_ }
    · intro h
      funext i
      simp
    · intro p
      ext i <;> simp
  · intro r j i
    exact hei i (r i) (j i)

/-- **The block decomposition of the shift-tuple sums.**  Reindexing the double sum over the shift
tuples in `∀ i, ↥(d_i[B · H'])` along the block equivalence turns it into a sum over the block
indices `jj : (∀ i, Fin B)²` of the double sum over the residue tuples in `∀ i, ↥(d_i[H'])`, the
argument of `Φ` acquiring the shift `d i · H' · (jj.1 i - jj.2 i)`. -/
theorem block_sum_gen {t : ℕ} {d : Fin t → ℤ} {B H' : ℕ}
    (e : (∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B * H')))
           ≃ ((∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) H')) × (∀ i : Fin t, Fin B)))
    (he : ∀ (r : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) H')) (j : ∀ i : Fin t, Fin B)
        (i : Fin t),
        ((e.symm (r, j)) i : ℤ) = (r i : ℤ) + d i * H' * (j i : ℤ))
    (Φ : (Fin t → ℤ) → ℂ) :
    (∑ h : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B * H')),
       ∑ h' : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B * H')),
         Φ (fun i => (h i : ℤ) - (h' i : ℤ)))
      = ∑ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
          ∑ r : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) H'),
            ∑ r' : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) H'),
              Φ ((fun i => (r i : ℤ) - (r' i : ℤ))
                  + (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
  classical
  let A := ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B * H'))
  let C := ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) H')
  let D := ∀ i : Fin t, Fin B
  calc (∑ h : A, ∑ h' : A, Φ (fun i => (h i : ℤ) - (h' i : ℤ)))
      = ∑ p : A × A, Φ (fun i => (p.1 i : ℤ) - (p.2 i : ℤ)) :=
        (Fintype.sum_prod_type' (f := fun (x y : A) => Φ (fun i => (x i : ℤ) - (y i : ℤ)))).symm
    _ = ∑ q : (C × D) × (C × D),
          Φ (fun i => ((e.symm q.1) i : ℤ) - ((e.symm q.2) i : ℤ)) :=
        Fintype.sum_equiv (Equiv.prodCongr e e) _ _
          (fun p => by simp [Equiv.prodCongr])
    _ = ∑ x : (C × C) × (D × D),
          Φ (fun i => ((e.symm (x.1.1, x.2.1)) i : ℤ) - ((e.symm (x.1.2, x.2.2)) i : ℤ)) :=
        Fintype.sum_equiv (Equiv.prodProdProdComm C D C D) _ _
          (fun q => by simp [Equiv.prodProdProdComm])
    _ = ∑ jj : D × D, ∑ rr : C × C,
          Φ (fun i => ((e.symm (rr.1, jj.1)) i : ℤ) - ((e.symm (rr.2, jj.2)) i : ℤ)) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
          ∑ r : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) H'),
            ∑ r' : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) H'),
              Φ ((fun i => (r i : ℤ) - (r' i : ℤ))
                  + (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
        refine Finset.sum_congr rfl (fun jj _ => ?_)
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun r' _ => ?_))
        refine congrArg Φ (funext (fun i => ?_))
        rw [he r jj.1 i, he r' jj.2 i]
        simp only [Pi.add_apply]
        ring

/-! ## The shrink inequality for a general direction tuple -/

/-- **The box-norm power is decreasing in the length of the arithmetic progressions.**  For
`H = B · H'` with `B, H' ≥ 1` and a non-zero direction tuple `d`, the level-`t` box-norm power of
`f` over the directions `d_i[B · H']` is at most the one over the directions `d_i[H']`. -/
theorem boxNormPow_arithIcc_shrink_gen {t : ℕ} (ht : 1 ≤ t) {d : Fin t → ℤ} (hd : ∀ i, d i ≠ 0)
    {B H' : ℕ} (hB : 1 ≤ B) (hH' : 1 ≤ H') (S : Finset ℤ) {f : ℤ → ℂ}
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (B * H')) S f
      ≤ Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S f := by
  classical
  have hcorner : ∀ (G : (Fin t → Bool) → ℤ → ℂ) (h h' : Fin t → ℤ),
      (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (G ω (x + Work.Peluse.cornerShift h h' ω)))
        = ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (G ω (x + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω)) :=
    fun G h h' => Work.Peluse.Concat.tsum_cube_corner_eq_shrink G h h'
  have hcardH : ∀ i : Fin t, (Work.Peluse.arithIcc (d i) (B * H')).card = B * H' :=
    fun i => Work.Peluse.Concat.card_arithIcc_shrink (hd i) (B * H')
  have hcardL : ∀ i : Fin t, (Work.Peluse.arithIcc (d i) H').card = H' :=
    fun i => Work.Peluse.Concat.card_arithIcc_shrink (hd i) H'
  obtain ⟨e, he⟩ := arithIcc_blockEquiv_gen (d := d) hd hB hH'
  have hPH : (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B * H')).card : ℂ))⁻¹)
      = ((B : ℂ))⁻¹ ^ t * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹) := by
    rw [show ((B : ℂ))⁻¹ ^ t = ∏ _ : Fin t, ((B : ℂ))⁻¹ by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hcardH i, hcardL i]
    push_cast
    ring
  set Sig : ℂ := ∑ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
      ∑ r : (i : Fin t) → ↥(Work.Peluse.arithIcc (d i) H'),
        ∑ r' : (i : Fin t) → ↥(Work.Peluse.arithIcc (d i) H'),
          Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f)
            ((fun i => (r i : ℤ) - (r' i : ℤ))
              + (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) with hSig
  have hfold : Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (B * H')) S
        (fun _ : Fin t → Bool => f)
      = ((S.card : ℂ))⁻¹
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B * H')).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B * H')).card : ℂ))⁻¹) * Sig := by
    rw [prodCubeSum_fold_gen (Q := fun i : Fin t => Work.Peluse.arithIcc (d i) (B * H')) S
        (hcorner (fun _ : Fin t → Bool => f)),
      block_sum_gen (d := d) (B := B) (H' := H') e he
        (Φ := fun u => Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f) u)]
  have hper : ∀ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
      Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
        (fun ω : Fin t → Bool => Work.Peluse.shift
          (Work.Peluse.cornerShift (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)
      = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹)
          * ∑ r : (i : Fin t) → ↥(Work.Peluse.arithIcc (d i) H'),
              ∑ r' : (i : Fin t) → ↥(Work.Peluse.arithIcc (d i) H'),
                Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f)
                  ((fun i => (r i : ℤ) - (r' i : ℤ))
                    + (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
    intro jj
    exact prodCubeSum_shiftFam_gen (Q := fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
      (F := fun _ : Fin t → Bool => f)
      (e := fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) hcorner
  have hsum : (∑ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
        Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
          (fun ω : Fin t → Bool => Work.Peluse.shift
            (Work.Peluse.cornerShift
              (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f))
      = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹) * Sig := by
    rw [Finset.sum_congr rfl (fun jj _ => hper jj), ← Finset.mul_sum, hSig]
  have hsc : ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B * H')).card : ℂ))⁻¹)
        * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B * H')).card : ℂ))⁻¹)
      = ((B : ℂ) ^ (2 * t))⁻¹ *
        (((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹)) := by
    have hpow : ((B : ℂ))⁻¹ ^ t * ((B : ℂ))⁻¹ ^ t = ((B : ℂ) ^ (2 * t))⁻¹ := by
      rw [← pow_add, show t + t = 2 * t by omega, ← inv_pow]
    rw [hPH]
    rw [show ((S.card : ℂ))⁻¹ * (((B : ℂ))⁻¹ ^ t * ∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹)
          * (((B : ℂ))⁻¹ ^ t * ∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹)
        = (((B : ℂ))⁻¹ ^ t * ((B : ℂ))⁻¹ ^ t) * ((S.card : ℂ))⁻¹
          * ((∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹)
            * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) H').card : ℂ))⁻¹)) by ring]
    rw [hpow]
    ring
  have hmain : Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (B * H')) S
        (fun _ : Fin t → Bool => f)
      = ((B : ℂ) ^ (2 * t))⁻¹ *
        ∑ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
          Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
            (fun ω : Fin t → Bool => Work.Peluse.shift
              (Work.Peluse.cornerShift
                (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f) := by
    rw [hfold, hsum, hsc]
    ring
  have hterm : ∀ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
      ‖Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
          (fun ω : Fin t → Bool => Work.Peluse.shift
            (Work.Peluse.cornerShift
              (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖
        ≤ Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S f := by
    intro jj
    have hfin : ∀ ω : Fin t → Bool, Work.Peluse.FinSuppZ
        (Work.Peluse.shift
          (Work.Peluse.cornerShift
            (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f) :=
      fun ω => Work.Peluse.Concat.finsupp_shift_shrink hf _
    have hgcs := Work.Peluse.BoxNorm.prodCubeSum_norm_le ht
      (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S _ hfin
    have hprod : (∏ ω : Fin t → Bool, Work.Peluse.boxNorm t
          (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
          (Work.Peluse.shift
            (Work.Peluse.cornerShift
              (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f))
        = Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S f := by
      have hpt : ∀ ω : Fin t → Bool, Work.Peluse.boxNorm t
            (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
            (Work.Peluse.shift
              (Work.Peluse.cornerShift
                (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)
          = (Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S f)
              ^ (1 / (2 : ℝ) ^ t) := by
        intro ω
        rw [Work.Peluse.boxNorm,
          Work.Peluse.BoxNorm.boxNormPow_shift t (fun i : Fin t => Work.Peluse.arithIcc (d i) H')
            S f _ hf]
      rw [Finset.prod_congr rfl (fun ω _ => hpt ω), Finset.prod_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Work.Peluse.BoxNorm.rpow_root_pow
        (norm_nonneg (Work.Peluse.boxSumPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S f)) t
    rw [← hprod]
    exact hgcs
  have hcard : ((Fintype.card ((∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B))) : ℝ)
      = ((B : ℝ)) ^ (2 * t) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
    rw [← pow_add, show t + t = 2 * t by omega]
  have hBne : ((B : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn : ‖((B : ℂ) ^ (2 * t))⁻¹‖ = (((B : ℝ)) ^ (2 * t))⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  rw [Work.Peluse.boxNormPow, Work.Peluse.boxSumPow, hmain]
  calc ‖((B : ℂ) ^ (2 * t))⁻¹ *
        ∑ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
          Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
            (fun ω : Fin t → Bool => Work.Peluse.shift
              (Work.Peluse.cornerShift
                (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖
      ≤ ‖((B : ℂ) ^ (2 * t))⁻¹‖ *
          ‖∑ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
            Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
              (fun ω : Fin t → Bool => Work.Peluse.shift
                (Work.Peluse.cornerShift
                  (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖ :=
        norm_mul_le _ _
    _ ≤ (((B : ℝ)) ^ (2 * t))⁻¹ *
          ∑ jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
            ‖Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S
              (fun ω : Fin t → Bool => Work.Peluse.shift
                (Work.Peluse.cornerShift
                  (fun i => d i * H' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖ := by
        rw [hn]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (((B : ℝ)) ^ (2 * t))⁻¹ *
          ∑ _jj : (∀ i : Fin t, Fin B) × (∀ i : Fin t, Fin B),
            Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S f := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum (fun jj _ => hterm jj)
    _ = Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S f := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ hBne), one_mul]

/-! ## The scale transfer in the form requested -/

/-- The shrink inequality with the long length written as `B · H'` and the identity
`H = B · H'` supplied as a hypothesis, so that it can be applied without a rewriting step. -/
theorem boxNormPow_arithIcc_shrink {t : ℕ} (ht : 1 ≤ t) {d : Fin t → ℤ} (hd : ∀ i, d i ≠ 0)
    {B H' H : ℕ} (hH : H = B * H') (hB : 1 ≤ B) (hH' : 1 ≤ H') (S : Finset ℤ) {f : ℤ → ℂ}
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H) S f
      ≤ Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H') S f := by
  subst hH
  exact boxNormPow_arithIcc_shrink_gen ht hd hB hH' S hf

theorem boxNormPow_scale_transfer {k : ℕ} (hk : 1 ≤ k) :
    ∃ c e : ℝ, 0 < c ∧ 0 ≤ e ∧
      ∀ {N : ℕ} (hN : 0 < N) (f : ℤ → ℂ), Work.Peluse.SupportIn f N → (∀ x, ‖f x‖ ≤ 1) →
      ∀ (d : Fin k → ℤ), (∀ i, d i ≠ 0) → ∀ {H' H : ℕ}, 1 ≤ H' → H' ≤ H → H' ∣ H →
      c * ((H' : ℝ) / (H : ℝ)) ^ e *
          Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H)
            (Work.Peluse.symIcc N) f
        ≤ Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H')
            (Work.Peluse.symIcc N) f := by
  refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
  intro N _hN f hsup _hbd d hd H' H hH' hle hdvd
  obtain ⟨B, hB⟩ := hdvd
  have hH : H = B * H' := by rw [hB, Nat.mul_comm]
  have hB1 : 1 ≤ B := by
    rcases Nat.eq_zero_or_pos B with hB0 | hBpos
    · rw [hB0, Nat.mul_zero] at hB
      omega
    · exact hBpos
  simp only [Real.rpow_zero, one_mul, mul_one]
  exact boxNormPow_arithIcc_shrink hk hd hH hB1 hH' (Work.Peluse.symIcc N)
    (Work.Peluse.FinSuppZ.of_supportIn hsup)

end

end Work.Peluse.PET
