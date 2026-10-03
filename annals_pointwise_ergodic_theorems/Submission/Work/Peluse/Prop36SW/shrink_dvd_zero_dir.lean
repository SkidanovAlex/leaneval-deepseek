import Mathlib
import Submission.Work.Peluse.TransferUp.boxNormPow_arithIcc_shrink_coord

/-!
# Shrinking the direction sets `q_i[B_i · L_i]` to `q_i[L_i]`, allowing zero directions

`Work.Peluse.TransferUp.boxNormPow_arithIcc_shrink_coord` proves that the level-`t` box norm power
over the directions `d_i[B_i · L_i]` is at most the one over `d_i[L_i]`, **for non-zero** `d_i`.

This file removes that restriction.  The only place where a zero direction could break the
argument is the block decomposition `d_i[B_i L_i] ≃ d_i[L_i] × Fin (B_i)`, which needs
`d_i ≠ 0`; when `d_i = 0` the two direction sets `q_i[B_i L_i]` and `q_i[L_i]` coincide as soon as
`B_i = 1` (each is the (possibly empty) singleton `{0}`), so that coordinate is a trivial factor
of the block decomposition.  The block decomposition of the remaining coordinates is unchanged, and
the cardinality bookkeeping is done coordinatewise (`card_arithIcc_mul_of_zero`).

The target is `Work.Peluse.Prop36SW.shrink_dvd_zero_dir`.
-/

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse

/-! ## Elementary per-coordinate facts -/

/-- A member of the arithmetic progression `c[m]` is `0` when `c = 0`. -/
lemma mem_arithIcc_zero {c : ℤ} {m : ℕ} {x : ℤ} (hc : c = 0)
    (hx : x ∈ Work.Peluse.arithIcc c m) : x = 0 := by
  obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hx
  rw [hc]
  simp

/-- `0` belongs to the arithmetic progression `0[m]` for `1 ≤ m`. -/
lemma zero_mem_arithIcc_zero {m : ℕ} (hm : 1 ≤ m) :
    (0 : ℤ) ∈ Work.Peluse.arithIcc (0 : ℤ) m := by
  refine Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hm⟩, ?_⟩
  simp

/-- **Cardinality of one coordinate.**  For `1 ≤ B` and `d = 0 → B = 1` the block `d[B · L]` has
`B` times as many elements as `d[L]`: for `d ≠ 0` both are arithmetic progressions of lengths
`B · L` and `L`, and for `d = 0` both sets are (possibly empty) singletons. -/
lemma card_arithIcc_mul_of_zero {d : ℤ} {B L : ℕ} (hB : 1 ≤ B) (hz : d = 0 → B = 1) :
    (Work.Peluse.arithIcc d (B * L)).card = B * (Work.Peluse.arithIcc d L).card := by
  by_cases hd : d = 0
  · obtain rfl : B = 1 := hz hd
    rw [hd, one_mul, one_mul]
  · rw [Work.Peluse.Concat.card_arithIcc_shrink hd (B * L),
      Work.Peluse.Concat.card_arithIcc_shrink hd L]

/-! ## The block decomposition, allowing zero directions -/

/-- **The block equivalence, allowing the zero direction.**  Under `d i = 0 → B i = 1`, the index
set `∀ i, ↥(d i[B i · L i])` is the product of `∀ i, ↥(d i[L i])` and the block index set
`∀ i, Fin (B i)`, with the coordinate description `(r, j) ↦ r i + d i · L i · (j i)`.

This is `Work.Peluse.TransferUp.arithIcc_blockEquiv_coord_aux` with the hypothesis `d i ≠ 0`
weakened: a zero coordinate carries `B i = 1`, hence its two direction sets coincide, so the
coordinate is a trivial factor. -/
theorem arithIcc_blockEquiv_coord_zero {t : ℕ} {d : Fin t → ℤ} {B L : Fin t → ℕ}
    (hB : ∀ i, 1 ≤ B i) (hz : ∀ i, d i = 0 → B i = 1) (hL : ∀ i, 1 ≤ L i) :
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
          = (r : ℤ) + d i * L i * (j : ℤ) := by
    intro i
    by_cases hz0 : d i = 0
    · -- the zero coordinate: both direction sets are (possibly empty) singletons
      have hB1 : B i = 1 := hz i hz0
      have hnonzero : 1 ≤ B i * L i := by rw [hB1, one_mul]; exact hL i
      have hmemL : (0 : ℤ) ∈ Work.Peluse.arithIcc (d i) (L i) := by
        rw [hz0]
        exact zero_mem_arithIcc_zero (hL i)
      have hmemH : (0 : ℤ) ∈ Work.Peluse.arithIcc (d i) (B i * L i) := by
        rw [hz0]
        exact zero_mem_arithIcc_zero hnonzero
      let e0 : ↥(Work.Peluse.arithIcc (d i) (B i * L i))
          ≃ (↥(Work.Peluse.arithIcc (d i) (L i)) × Fin (B i)) :=
        { toFun := fun a => (⟨(a : ℤ), by
              have h0 : (a : ℤ) = 0 := mem_arithIcc_zero hz0 a.2
              rw [h0]
              exact hmemL⟩, ⟨0, by have h := hB i; omega⟩)
          invFun := fun p => ⟨(p.1 : ℤ), by
              have h0 : (p.1 : ℤ) = 0 := mem_arithIcc_zero hz0 p.1.2
              rw [h0]
              exact hmemH⟩
          left_inv := fun a => Subtype.ext rfl
          right_inv := fun p => Prod.ext (Subtype.ext rfl)
            (Fin.ext (by
              show (0 : ℕ) = (p.2 : ℕ)
              have := p.2.isLt
              omega)) }
      refine ⟨e0, ?_⟩
      intro r j
      have hval : ((e0.symm (r, j) : ↥(Work.Peluse.arithIcc (d i) (B i * L i))) : ℤ) = (r : ℤ) :=
        rfl
      have hzero : d i * (L i : ℤ) * (j : ℤ) = 0 := by rw [hz0]; ring
      rw [hval, hzero, add_zero]
    · -- the generic coordinate: the block decomposition for a non-zero direction
      exact Work.Peluse.Concat.arithIcc_blockEquiv_shrink (c := d i) hz0 (L' := L i) (m := B i)
        (L := B i * L i) rfl (hL i) (hB i)
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

/-! ## The shrink inequality -/

theorem shrink_dvd_zero_dir {t : ℕ} (ht : 1 ≤ t) (q : Fin t → ℤ) (B L : Fin t → ℕ)
    (hB : ∀ i, 1 ≤ B i) (hz : ∀ i, q i = 0 → B i = 1) (hL : ∀ i, 1 ≤ L i)
    (S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (B i * L i)) S f
      ≤ Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (L i)) S f := by
  classical
  have hcorner : ∀ (G : (Fin t → Bool) → ℤ → ℂ) (h h' : Fin t → ℤ),
      (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (G ω (x + Work.Peluse.cornerShift h h' ω)))
        = ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (G ω (x + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω)) :=
    fun G h h' => Work.Peluse.Concat.tsum_cube_corner_eq_shrink G h h'
  have hcardrel : ∀ i : Fin t, (Work.Peluse.arithIcc (q i) (B i * L i)).card
      = B i * (Work.Peluse.arithIcc (q i) (L i)).card :=
    fun i => card_arithIcc_mul_of_zero (hB i) (hz i)
  obtain ⟨e, he⟩ := arithIcc_blockEquiv_coord_zero (d := q) hB hz hL
  have hPH : (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (B i * L i)).card : ℂ))⁻¹)
      = (∏ i : Fin t, ((B i : ℂ))⁻¹)
        * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hcardrel i, Nat.cast_mul, mul_inv]
  set Sig : ℂ := ∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
      ∑ r : (i : Fin t) → ↥(Work.Peluse.arithIcc (q i) (L i)),
        ∑ r' : (i : Fin t) → ↥(Work.Peluse.arithIcc (q i) (L i)),
          Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f)
            ((fun i => (r i : ℤ) - (r' i : ℤ))
              + (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) with hSig
  have hfold : Work.Peluse.prodCubeSum t
        (fun i : Fin t => Work.Peluse.arithIcc (q i) (B i * L i)) S
        (fun _ : Fin t → Bool => f)
      = ((S.card : ℂ))⁻¹
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (B i * L i)).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (B i * L i)).card : ℂ))⁻¹) * Sig := by
    rw [Work.Peluse.PET.prodCubeSum_fold_gen
        (Q := fun i : Fin t => Work.Peluse.arithIcc (q i) (B i * L i)) S
        (hcorner (fun _ : Fin t → Bool => f)),
      Work.Peluse.TransferUp.block_sum_coord_aux (d := q) (B := B) (L := L) e he
        (Φ := fun u => Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f) u)]
  have hper : ∀ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
      Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
        (fun ω : Fin t → Bool => Work.Peluse.shift
          (Work.Peluse.cornerShift (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)
      = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹)
          * ∑ r : (i : Fin t) → ↥(Work.Peluse.arithIcc (q i) (L i)),
              ∑ r' : (i : Fin t) → ↥(Work.Peluse.arithIcc (q i) (L i)),
                Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f)
                  ((fun i => (r i : ℤ) - (r' i : ℤ))
                    + (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
    intro jj
    exact Work.Peluse.PET.prodCubeSum_shiftFam_gen
      (Q := fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
      (F := fun _ : Fin t → Bool => f)
      (e := fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) hcorner
  have hsum : (∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
        Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
          (fun ω : Fin t → Bool => Work.Peluse.shift
            (Work.Peluse.cornerShift
              (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f))
      = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹) * Sig := by
    rw [Finset.sum_congr rfl (fun jj _ => hper jj), ← Finset.mul_sum, hSig]
  have hpow : (∏ i : Fin t, ((B i : ℂ))⁻¹) * (∏ i : Fin t, ((B i : ℂ))⁻¹)
      = ((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹ := by
    rw [Finset.prod_inv_distrib, ← mul_inv]
    congr 1
    rw [pow_two]
  have hsc : ((S.card : ℂ))⁻¹
        * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (B i * L i)).card : ℂ))⁻¹)
        * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (B i * L i)).card : ℂ))⁻¹)
      = ((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹ *
        (((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹)
          * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹)) := by
    rw [hPH]
    rw [show ((S.card : ℂ))⁻¹
          * ((∏ i : Fin t, ((B i : ℂ))⁻¹)
            * ∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹)
          * ((∏ i : Fin t, ((B i : ℂ))⁻¹)
            * ∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹)
        = ((∏ i : Fin t, ((B i : ℂ))⁻¹) * (∏ i : Fin t, ((B i : ℂ))⁻¹)) * ((S.card : ℂ))⁻¹
          * ((∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹)
            * (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (L i)).card : ℂ))⁻¹)) by ring]
    rw [hpow]
    ring
  have hmain : Work.Peluse.prodCubeSum t
        (fun i : Fin t => Work.Peluse.arithIcc (q i) (B i * L i)) S
        (fun _ : Fin t → Bool => f)
      = ((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹ *
        ∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
          Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
            (fun ω : Fin t → Bool => Work.Peluse.shift
              (Work.Peluse.cornerShift
                (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f) := by
    rw [hfold, hsum, hsc]
    ring
  have hterm : ∀ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
      ‖Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
          (fun ω : Fin t → Bool => Work.Peluse.shift
            (Work.Peluse.cornerShift
              (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖
        ≤ Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S f := by
    intro jj
    have hfin : ∀ ω : Fin t → Bool, Work.Peluse.FinSuppZ
        (Work.Peluse.shift
          (Work.Peluse.cornerShift
            (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f) :=
      fun ω => Work.Peluse.Concat.finsupp_shift_shrink hf _
    have hgcs := Work.Peluse.BoxNorm.prodCubeSum_norm_le ht
      (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S _ hfin
    have hprod : (∏ ω : Fin t → Bool, Work.Peluse.boxNorm t
          (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
          (Work.Peluse.shift
            (Work.Peluse.cornerShift
              (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f))
        = Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S f := by
      have hpt : ∀ ω : Fin t → Bool, Work.Peluse.boxNorm t
            (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
            (Work.Peluse.shift
              (Work.Peluse.cornerShift
                (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)
          = (Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S f)
              ^ (1 / (2 : ℝ) ^ t) := by
        intro ω
        rw [Work.Peluse.boxNorm,
          Work.Peluse.BoxNorm.boxNormPow_shift t
            (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S f _ hf]
      rw [Finset.prod_congr rfl (fun ω _ => hpt ω), Finset.prod_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Work.Peluse.BoxNorm.rpow_root_pow
        (norm_nonneg (Work.Peluse.boxSumPow t
          (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S f)) t
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
          Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
            (fun ω : Fin t → Bool => Work.Peluse.shift
              (Work.Peluse.cornerShift
                (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖
      ≤ ‖((∏ i : Fin t, ((B i : ℂ))) ^ 2)⁻¹‖ *
          ‖∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
            Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
              (fun ω : Fin t → Bool => Work.Peluse.shift
                (Work.Peluse.cornerShift
                  (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖ :=
        norm_mul_le _ _
    _ ≤ (((∏ i : Fin t, (B i : ℝ))) ^ 2)⁻¹ *
          ∑ jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
            ‖Work.Peluse.prodCubeSum t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S
              (fun ω : Fin t → Bool => Work.Peluse.shift
                (Work.Peluse.cornerShift
                  (fun i => q i * L i * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖ := by
        rw [hn]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (((∏ i : Fin t, (B i : ℝ))) ^ 2)⁻¹ *
          ∑ _jj : (∀ i : Fin t, Fin (B i)) × (∀ i : Fin t, Fin (B i)),
            Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S f := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum (fun jj _ => hterm jj)
    _ = Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (q i) (L i)) S f := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ hBne), one_mul]

end

end Work.Peluse.Prop36SW
