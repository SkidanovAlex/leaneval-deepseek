/-
  WilE9 / Sharp / PbDet — the stratum rows of the pulled-back fibre Jacobian.

  The rows of `Mmat` carrying the stratum equations `h a` are computed by the chain rule for
  `rename` (`eaD_pbRaise`): the entry at column `l` is a sum over the stratum's coordinates
  `Fin (n + (1 + m))`, namely `∑ i, [sIdxPb i = natAdd n l] · ∂h a / ∂i`.  The stratum coordinate
  `i` corresponds to the fibre index `kap n m i` (`y i`, `τ` or `aux b`), so the sum against a
  vector supported off the `y`-coordinates is exactly the `(τ, aux)`-system of `Hmat`
  (`Mmat_mulVec_hRow`).
-/
import Submission.Work.WilE9.Sharp.PbDet.RowEntries
import Submission.Work.WilE9.Sharp.eaD_pbRaise

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

section HRow

variable {n m r : ℕ}

theorem kap_castAdd (i : Fin n) : kap n m (Fin.castAdd (1 + m) i) = fY n m i := by
  rw [kap, dif_pos (by simp only [Fin.castAdd, Fin.val_mk]; exact i.isLt)]
  first
    | rfl
    | (congr 1; apply Fin.ext; simp only [Fin.castAdd, Fin.val_mk])

theorem kap_natAdd (l : Fin (1 + m)) : kap n m (Fin.natAdd n l) = hColIdx n m l := by
  by_cases hl : (l : ℕ) = 0
  · have h0 : l = 0 := Fin.ext hl
    subst h0
    rw [hColIdx_zero]
    rw [kap, dif_neg (by simp only [Fin.natAdd, Fin.val_mk]; omega),
      dif_pos (by simp only [Fin.natAdd, Fin.val_mk]; omega)]
  · rw [kap, dif_neg (by simp only [Fin.natAdd, Fin.val_mk]; omega),
      dif_neg (by simp only [Fin.natAdd, Fin.val_mk]; omega), hColIdx_of_ne_zero hl]
    congr 1
    apply Fin.ext
    simp only [Fin.natAdd, Fin.val_mk]
    omega

theorem sIdxPb_kap (i : Fin (n + (1 + m))) : sIdxPb n m i = ambIdx n m (kap n m i) := by
  by_cases h1 : (i : ℕ) < n
  · rw [sIdxPb, dif_pos h1, kap, dif_pos h1]
    exact (natAdd_fY_val (n := n) (m := m) ⟨(i : ℕ), h1⟩).symm.trans (by rw [ambIdx])
  · by_cases h2 : (i : ℕ) = n
    · rw [sIdxPb, dif_neg h1, dif_pos h2, kap, dif_neg h1, dif_pos h2]
      exact (natAdd_fT_val (n := n) (m := m)).symm.trans (by rw [ambIdx])
    · rw [sIdxPb, dif_neg h1, dif_neg h2, kap, dif_neg h1, dif_neg h2]
      exact (natAdd_fA_val (n := n) (m := m)
        ⟨(i : ℕ) - (n + 1), by have := i.isLt; omega⟩).symm.trans (by rw [ambIdx])

theorem ambIdx_inj {l l' : Fin (qpb n m)} (hh : ambIdx n m l = ambIdx n m l') : l = l' := by
  have h1 := congrArg Fin.val hh
  simp only [ambIdx, Fin.natAdd, Fin.val_mk] at h1
  exact Fin.ext (by omega)

theorem sIdxPb_eq_ambIdx_iff (i : Fin (n + (1 + m))) (l : Fin (qpb n m)) :
    (sIdxPb n m i = ambIdx n m l) ↔ (l = kap n m i) := by
  rw [sIdxPb_kap (n := n) (m := m) i]
  exact ⟨fun hh => (ambIdx_inj hh).symm, fun hh => by rw [hh]⟩

theorem sum_kap (i : Fin (n + (1 + m))) (v : Fin (qpb n m) → ℝ) :
    (∑ l : Fin (qpb n m), (if sIdxPb n m i = ambIdx n m l then v l else 0))
      = v (kap n m i) := by
  have h1 : ∀ l : Fin (qpb n m),
      (if sIdxPb n m i = ambIdx n m l then v l else 0) = (if l = kap n m i then v l else 0) := by
    intro l
    simp only [sIdxPb_eq_ambIdx_iff i l]
  rw [Finset.sum_congr rfl (fun l _ => h1 l)]
  simp

theorem pbF_hRow (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (a : Fin (1 + m)) :
    pbF n m r h (hRow n m a) = pbRaise (n := n) (m := m) (r := r) (h a) := by
  rw [pbF]
  rw [dif_neg (by rw [hRow_val]; omega), dif_neg (by rw [hRow_val]; omega),
    dif_neg (by rw [hRow_val]; omega), dif_neg (by rw [hRow_val]; omega)]
  refine congrArg (pbRaise (n := n) (m := m) (r := r)) (congrArg h ?_)
  apply Fin.ext
  simp only [hRow_val]
  omega

theorem Mmat_mulVec_hRow (c : EAChain (n + (1 + m)) r) (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (z : Fin (Npb n m) → ℝ) (v : Fin (qpb n m) → ℝ)
    (hv : ∀ i : Fin n, v (fY n m i) = 0) (a : Fin (1 + m)) :
    (Mmat n m r c h z).mulVec v (hRow n m a) = (Hmat n m r c h z).mulVec (wVec v) a := by
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct]
  have hrow : ∀ l : Fin (qpb n m), Mmat n m r c h z (hRow n m a) l
      = ∑ i : Fin (n + (1 + m)),
          (if sIdxPb n m i = ambIdx n m l then eaEval c (eaD c i (h a)) (pbStrat z) else 0) := by
    intro l
    rw [Mmat_apply, pbF_hRow h]
    exact eaD_pbRaise c (h a) z (ambIdx n m l)
  have hstep : ∀ i : Fin (n + (1 + m)),
      (∑ l : Fin (qpb n m),
          (if sIdxPb n m i = ambIdx n m l then eaEval c (eaD c i (h a)) (pbStrat z) else 0) * v l)
        = eaEval c (eaD c i (h a)) (pbStrat z) * v (kap n m i) := by
    intro i
    have h1 : ∀ l : Fin (qpb n m),
        (if sIdxPb n m i = ambIdx n m l then eaEval c (eaD c i (h a)) (pbStrat z) else 0) * v l
          = eaEval c (eaD c i (h a)) (pbStrat z)
            * (if sIdxPb n m i = ambIdx n m l then v l else 0) := by
      intro l; rw [ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_congr rfl (fun l _ => h1 l), ← Finset.mul_sum, sum_kap i v]
  rw [Finset.sum_congr rfl (fun l _ => by rw [hrow l, Finset.sum_mul]), Finset.sum_comm,
    show (∑ i : Fin (n + (1 + m)), ∑ l : Fin (qpb n m),
        (if sIdxPb n m i = ambIdx n m l then eaEval c (eaD c i (h a)) (pbStrat z) else 0) * v l)
      = ∑ i : Fin (n + (1 + m)), eaEval c (eaD c i (h a)) (pbStrat z) * v (kap n m i)
      from Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [Fin.sum_univ_add (f := fun i => eaEval c (eaD c i (h a)) (pbStrat z) * v (kap n m i)),
    Finset.sum_eq_zero (fun i _ => by rw [kap_castAdd, hv i, mul_zero]), zero_add]
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  simp only [Hmat_apply, wVec_apply, kap_natAdd]

end HRow

end Work.WilE9.Sharp
