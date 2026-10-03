import Mathlib
import Submission.Work.Peluse.PET.boxNormPow_scale_transfer

/-!
# Shrinking the arithmetic-progression direction sets, coordinatewise

The main theorem is `Work.Peluse.TransferUp.boxNormPow_arithIcc_shrink_coord`: for a non-zero
direction tuple `d`, lengths `L_i ≥ 1`, dilation factors `B_i ≥ 1`, a window `S` and a finitely
supported `f`, the level-`t` box-norm power over the directions `d_i[B_i · L_i]` is at most the
one over the directions `d_i[L_i]`.

This is the coordinatewise refinement of `Work.Peluse.PET.boxNormPow_arithIcc_shrink_gen`, whose
proof is repeated here with `B` and `H'` promoted to the families `B i` and `L i`.  The two
ingredients are the block decomposition of `d_i[B_i L_i]` into `B_i` blocks of `d_i[L_i]`
(`arithIcc_blockEquiv_coord_aux`) and the corresponding reindexing of the shift-tuple double sum
(`block_sum_coord_aux`); the rest is Gowers–Cauchy–Schwarz plus the cancellation of the `B_i`
against the cardinality ratio.
-/

set_option maxHeartbeats 1600000

namespace Work.Peluse.TransferUp

noncomputable section

open Work.Peluse

theorem arithIcc_blockEquiv_coord_aux {t : ℕ} {d : Fin t → ℤ} (hd : ∀ i, d i ≠ 0) {B L : Fin t → ℕ}
    (hB : ∀ i, 1 ≤ B i) (hL : ∀ i, 1 ≤ L i) :
    ∃ e : (∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B i * L i)))
          ≃ ((∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (L i))) × (∀ i : Fin t, Fin (B i))),
      ∀ (r : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (L i))) (j : ∀ i : Fin t, Fin (B i))
        (i : Fin t),
        ((e.symm (r, j)) i : ℤ) = (r i : ℤ) + d i * L i * (j i : ℤ) := by
  classical
  have hcoord : ∀ i : Fin t, ∃ ei : ↥(Work.Peluse.arithIcc (d i) (B i * L i))
      ≃ (↥(Work.Peluse.arithIcc (d i) (L i)) × Fin (B i)),
      ∀ (r : ↥(Work.Peluse.arithIcc (d i) (L i))) (j : Fin (B i)),
        ((ei.symm (r, j) : ↥(Work.Peluse.arithIcc (d i) (B i * L i))) : ℤ)
          = (r : ℤ) + d i * L i * (j : ℤ) :=
    fun i => Work.Peluse.Concat.arithIcc_blockEquiv_shrink (c := d i) (hd i) (L' := L i)
      (m := B i) (L := B i * L i) rfl (hL i) (hB i)
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

theorem block_sum_coord_aux {t : ℕ} {d : Fin t → ℤ} {B L : Fin t → ℕ}
    (e : (∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B i * L i)))
          ≃ ((∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (L i))) × (∀ i : Fin t, Fin (B i))))
    (he : ∀ (r : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (L i))) (j : ∀ i : Fin t, Fin (B i))
        (i : Fin t),
        ((e.symm (r, j)) i : ℤ) = (r i : ℤ) + d i * L i * (j i : ℤ))
    (Φ : (Fin t → ℤ) → ℂ) :
    (∑ h : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B i * L i)),
       ∑ h' : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B i * L i)),
         Φ (fun i => (h i : ℤ) - (h' i : ℤ)))
      = ∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
          ∑ r : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (L i)),
            ∑ r' : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (L i)),
              Φ ((fun i => (r i : ℤ) - (r' i : ℤ))
                  + (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
  classical
  let A := ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (B i * L i))
  let C := ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (L i))
  let D := ∀ i : Fin t, Fin (B i)
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
    _ = ∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
          ∑ r : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (L i)),
            ∑ r' : ∀ i : Fin t, ↥(Work.Peluse.arithIcc (d i) (L i)),
              Φ ((fun i => (r i : ℤ) - (r' i : ℤ))
                  + (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
        refine Finset.sum_congr rfl (fun jj _ => ?_)
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun r' _ => ?_))
        refine congrArg Φ (funext (fun i => ?_))
        rw [he r jj.1 i, he r' jj.2 i]
        simp only [Pi.add_apply]
        ring

theorem boxNormPow_arithIcc_shrink_coord {t : ℕ} (ht : 1 ≤ t) {d : Fin t → ℤ} (hd : ∀ i, d i ≠ 0)
    {B L : Fin t → ℕ} (hB : ∀ i, 1 ≤ B i) (hL : ∀ i, 1 ≤ L i) (S : Finset ℤ) {f : ℤ → ℂ}
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (B i * L i)) S f
      ≤ Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S f := by
  classical
  have hcorner : ∀ (G : (Fin t → Bool) → ℤ → ℂ) (h h' : Fin t → ℤ),
      (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (G ω (x + Work.Peluse.cornerShift h h' ω)))
        = ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (G ω (x + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω)) :=
    fun G h h' => Work.Peluse.Concat.tsum_cube_corner_eq_shrink G h h'
  have hcardH : ∀ i : Fin t, (Work.Peluse.arithIcc (d i) (B i * L i)).card = B i * L i :=
    fun i => Work.Peluse.Concat.card_arithIcc_shrink (hd i) (B i * L i)
  have hcardL : ∀ i : Fin t, (Work.Peluse.arithIcc (d i) (L i)).card = L i :=
    fun i => Work.Peluse.Concat.card_arithIcc_shrink (hd i) (L i)
  obtain ⟨e, he⟩ := arithIcc_blockEquiv_coord_aux (d := d) hd hB hL
  have hPH : (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B i * L i)).card : ℂ))⁻¹)
      = (∏ i : Fin t, ((B i : ℂ))⁻¹)
        * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hcardH i, hcardL i]
    push_cast
    ring
  set Sig : ℂ := ∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
      ∑ r : (i : Fin t) → ↥(Work.Peluse.arithIcc (d i) (L i)),
        ∑ r' : (i : Fin t) → ↥(Work.Peluse.arithIcc (d i) (L i)),
          Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f)
            ((fun i => (r i : ℤ) - (r' i : ℤ))
              + (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) with hSig
  have hfold : Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (B i * L i)) S
        (fun _ : Fin t → Bool => f)
      = ((S.card : ℂ))⁻¹
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B i * L i)).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B i * L i)).card : ℂ))⁻¹) * Sig := by
    rw [Work.Peluse.PET.prodCubeSum_fold_gen (Q := fun i : Fin t => Work.Peluse.arithIcc (d i) (B i * L i)) S
        (hcorner (fun _ : Fin t → Bool => f)),
      block_sum_coord_aux (d := d) (B := B) (L := L) e he
        (Φ := fun u => Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f) u)]
  have hper : ∀ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
      Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
        (fun ω : Fin t → Bool => Work.Peluse.shift
          (Work.Peluse.cornerShift (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)
      = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹)
          * ∑ r : (i : Fin t) → ↥(Work.Peluse.arithIcc (d i) (L i)),
              ∑ r' : (i : Fin t) → ↥(Work.Peluse.arithIcc (d i) (L i)),
                Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f)
                  ((fun i => (r i : ℤ) - (r' i : ℤ))
                    + (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
    intro jj
    exact Work.Peluse.PET.prodCubeSum_shiftFam_gen (Q := fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
      (F := fun _ : Fin t → Bool => f)
      (e := fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) hcorner
  have hsum : (∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
        Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
          (fun ω : Fin t → Bool => Work.Peluse.shift
            (Work.Peluse.cornerShift
              (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f))
      = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹) * Sig := by
    rw [Finset.sum_congr rfl (fun jj _ => hper jj), ← Finset.mul_sum, hSig]
  have hpow : (∏ i : Fin t, ((B i : ℂ))⁻¹) * (∏ i : Fin t, ((B i : ℂ))⁻¹)
      = ((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹ := by
    rw [Finset.prod_inv_distrib, ← mul_inv]
    congr 1
    rw [pow_two]
  have hsc : ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B i * L i)).card : ℂ))⁻¹)
        * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (B i * L i)).card : ℂ))⁻¹)
      = ((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹ *
        (((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹)) := by
    rw [hPH]
    rw [show ((S.card : ℂ))⁻¹
          * ((∏ i : Fin t, ((B i : ℂ))⁻¹) * ∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹)
          * ((∏ i : Fin t, ((B i : ℂ))⁻¹) * ∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹)
        = ((∏ i : Fin t, ((B i : ℂ))⁻¹) * (∏ i : Fin t, ((B i : ℂ))⁻¹)) * ((S.card : ℂ))⁻¹
          * ((∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹)
            * (∏ i : Fin t, (((Work.Peluse.arithIcc (d i) (L i)).card : ℂ))⁻¹)) by ring]
    rw [hpow]
    ring
  have hmain : Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (B i * L i)) S
        (fun _ : Fin t → Bool => f)
      = ((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹ *
        ∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
          Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
            (fun ω : Fin t → Bool => Work.Peluse.shift
              (Work.Peluse.cornerShift
                (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f) := by
    rw [hfold, hsum, hsc]
    ring
  have hterm : ∀ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
      ‖Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
          (fun ω : Fin t → Bool => Work.Peluse.shift
            (Work.Peluse.cornerShift
              (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖
        ≤ Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S f := by
    intro jj
    have hfin : ∀ ω : Fin t → Bool, Work.Peluse.FinSuppZ
        (Work.Peluse.shift
          (Work.Peluse.cornerShift
            (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f) :=
      fun ω => Work.Peluse.Concat.finsupp_shift_shrink hf _
    have hgcs := Work.Peluse.BoxNorm.prodCubeSum_norm_le ht
      (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S _ hfin
    have hprod : (∏ ω : Fin t → Bool, Work.Peluse.boxNorm t
          (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
          (Work.Peluse.shift
            (Work.Peluse.cornerShift
              (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f))
        = Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S f := by
      have hpt : ∀ ω : Fin t → Bool, Work.Peluse.boxNorm t
            (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
            (Work.Peluse.shift
              (Work.Peluse.cornerShift
                (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)
          = (Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S f)
              ^ (1 / (2 : ℝ) ^ t) := by
        intro ω
        rw [Work.Peluse.boxNorm,
          Work.Peluse.BoxNorm.boxNormPow_shift t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i))
            S f _ hf]
      rw [Finset.prod_congr rfl (fun ω _ => hpt ω), Finset.prod_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Work.Peluse.BoxNorm.rpow_root_pow
        (norm_nonneg (Work.Peluse.boxSumPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S f)) t
    rw [← hprod]
    exact hgcs
  have hcard : ((Fintype.card ((∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)))) : ℝ)
      = ((∏ i : Fin t, (B i : ℝ))) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
    push_cast
    ring
  have hBne : (∏ i : Fin t, (B i : ℝ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => Nat.cast_ne_zero.mpr (by have := hB i; omega)
  have hn : ‖((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹‖ = (((∏ i : Fin t, (B i : ℝ))) ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow, norm_prod]
    simp only [Complex.norm_natCast]
  rw [Work.Peluse.boxNormPow, Work.Peluse.boxSumPow, hmain]
  calc ‖((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹ *
        ∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
          Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
            (fun ω : Fin t → Bool => Work.Peluse.shift
              (Work.Peluse.cornerShift
                (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖
      ≤ ‖((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹‖ *
          ‖∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
            Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
              (fun ω : Fin t → Bool => Work.Peluse.shift
                (Work.Peluse.cornerShift
                  (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖ :=
        norm_mul_le _ _
    _ ≤ (((∏ i : Fin t, (B i : ℝ))) ^ 2)⁻¹ *
          ∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
            ‖Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S
              (fun ω : Fin t → Bool => Work.Peluse.shift
                (Work.Peluse.cornerShift
                  (fun i => d i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖ := by
        rw [hn]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (((∏ i : Fin t, (B i : ℝ))) ^ 2)⁻¹ *
          ∑ _jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
            Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S f := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum (fun jj _ => hterm jj)
    _ = Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) (L i)) S f := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ hBne), one_mul]


end

end Work.Peluse.TransferUp
