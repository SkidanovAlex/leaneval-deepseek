import Mathlib
import Submission.Work.Peluse.LadderP.boxNormPow_dilate_split

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- A nonzero dilation does not change the cardinality of an arithmetic progression `arithIcc`:
multiplication by `c ≠ 0` is a bijection `arithIcc a L ≃ arithIcc (c * a) L` (which is also correct
for `a = 0`, when both sets are the singleton `{0}`). -/
lemma card_arithIcc_mul_eq {c : ℤ} (hc : c ≠ 0) (a : ℤ) (L : ℕ) :
    (arithIcc (c * a) L).card = (arithIcc a L).card := by
  rw [← Fintype.card_coe (arithIcc (c * a) L), ← Fintype.card_coe (arithIcc a L)]
  exact (Fintype.card_congr (dilateEquiv c hc a L)).symm

/-- The dilation-splitting identity for the box-norm power, **without** the hypothesis that the
directions `q i` are nonzero.  When some `q i = 0` the corresponding direction set is the singleton
`{0}` on both sides; relative to `boxNormPow_dilate_split` the only change is that the normalising
factors `(card (arithIcc (c * q i) L))⁻¹` and `(card (arithIcc (q i) L))⁻¹` are equal to each other
rather than both equal to `L⁻¹`. -/
theorem p2dilateSplit {t : ℕ} (ht : 1 ≤ t) {c : ℤ} (hc : 0 < c)
    {q : Fin t → ℤ} {L N : ℕ} (hL : 1 ≤ L) (hcN : c ≤ 2 * (N : ℤ) + 1) {f : ℤ → ℂ}
    (hfs : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (c * q i) L)
        (Work.Peluse.symIcc N) f
      = ∑ r ∈ Finset.range c.natAbs,
          ((((Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card : ℝ)
              / (((Work.Peluse.symIcc N).card : ℝ)))
            * Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (q i) L)
                ((Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ)))
                (fun ξ : ℤ => f ((r : ℤ) + c * ξ)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  obtain ⟨M, hM⟩ := hfs
  -- the cardinalities of the direction sets are unchanged by the dilation (this is the only place
  -- where the hypothesis `q i ≠ 0` of `boxNormPow_dilate_split` was used)
  have hcard : ∀ i : Fin t, ((arithIcc (c * q i) L).card) = ((arithIcc (q i) L).card) :=
    fun i => card_arithIcc_mul_eq hcne (q i) L
  -- ------------------------------------------------------------------
  -- Step 1: the `rawSum` identity
  -- ------------------------------------------------------------------
  have hraw : BoxNorm.rawSum t (fun i : Fin t => arithIcc (c * q i) L) f
      = ∑ r ∈ Finset.range c.natAbs,
          BoxNorm.rawSum t (fun i : Fin t => arithIcc (q i) L)
            (fun ξ : ℤ => f ((r : ℤ) + c * ξ)) := by
    have hrawL : BoxNorm.rawSum t (fun i : Fin t => arithIcc (c * q i) L) f
        = ∑ H : (i : Fin t) → {x : ℤ // x ∈ arithIcc (c * q i) L},
            ∑ H' : (i : Fin t) → {x : ℤ // x ∈ arithIcc (c * q i) L},
              ∑' x : ℤ, CT f (fun i => (H i).1) (fun i => (H' i).1) x :=
      rawSum_eq_CT t (fun i : Fin t => arithIcc (c * q i) L) f
    have hrawR : ∀ r : ℕ,
        BoxNorm.rawSum t (fun i : Fin t => arithIcc (q i) L)
            (fun ξ : ℤ => f ((r : ℤ) + c * ξ))
          = ∑ h : (i : Fin t) → {x : ℤ // x ∈ arithIcc (q i) L},
              ∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc (q i) L},
                ∑' ξ : ℤ,
                  CT (fun ξ : ℤ => f ((r : ℤ) + c * ξ)) (fun i => (h i).1) (fun i => (h' i).1) ξ :=
      fun r => rawSum_eq_CT t (fun i : Fin t => arithIcc (q i) L)
        (fun ξ : ℤ => f ((r : ℤ) + c * ξ))
    rw [hrawL]
    rw [show (∑ r ∈ Finset.range c.natAbs,
            BoxNorm.rawSum t (fun i : Fin t => arithIcc (q i) L)
              (fun ξ : ℤ => f ((r : ℤ) + c * ξ)))
        = ∑ r ∈ Finset.range c.natAbs,
            ∑ h : (i : Fin t) → {x : ℤ // x ∈ arithIcc (q i) L},
              ∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc (q i) L},
                ∑' ξ : ℤ,
                  CT (fun ξ : ℤ => f ((r : ℤ) + c * ξ)) (fun i => (h i).1) (fun i => (h' i).1) ξ
        from Finset.sum_congr rfl (fun r _ => hrawR r)]
    -- the reindexing of the two shift tuples
    have hre : (∑ H : (i : Fin t) → {x : ℤ // x ∈ arithIcc (c * q i) L},
          ∑ H' : (i : Fin t) → {x : ℤ // x ∈ arithIcc (c * q i) L},
            ∑' x : ℤ, CT f (fun i => (H i).1) (fun i => (H' i).1) x)
        = ∑ h : (i : Fin t) → {x : ℤ // x ∈ arithIcc (q i) L},
            ∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc (q i) L},
              ∑' x : ℤ, CT f (fun i => c * (h i).1) (fun i => c * (h' i).1) x := by
      rw [sum_pi_dilate hcne q L (F := fun H =>
        ∑ H' : (i : Fin t) → {x : ℤ // x ∈ arithIcc (c * q i) L},
          ∑' x : ℤ, CT f (fun i => (H i).1) (fun i => (H' i).1) x)]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [sum_pi_dilate hcne q L (F := fun H' =>
        ∑' x : ℤ, CT f (fun i => (dilatePi c q L h i).1) (fun i => (H' i).1) x)]
      refine Finset.sum_congr rfl (fun h' _ => ?_)
      exact tsum_congr (fun x => by simp only [dilatePi])
    -- the residue splitting of the `x`-sum
    have hsplit : ∀ (h h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc (q i) L}),
        (∑' x : ℤ, CT f (fun i => c * (h i).1) (fun i => c * (h' i).1) x)
          = ∑ r ∈ Finset.range c.natAbs,
              ∑' ξ : ℤ, CT (fun ξ : ℤ => f ((r : ℤ) + c * ξ))
                (fun i => (h i).1) (fun i => (h' i).1) ξ := by
      intro h h'
      have hv : ∀ x : ℤ, M + (∑ i, (q i).natAbs) * L * c.natAbs < x.natAbs →
          CT f (fun i => c * (h i).1) (fun i => c * (h' i).1) x = 0 := by
        intro x hx
        rw [CT_eq_prod_c]
        exact prod_cubeTerm_vanishes hc hM h h' x hx
      rw [tsum_mod_split hcne hv]
      refine Finset.sum_congr rfl (fun r _ => tsum_congr (fun ξ => ?_))
      exact CT_dilate_arg f c r (fun i => (h i).1) (fun i => (h' i).1) ξ
    exact hre.trans <| (Finset.sum_congr rfl (fun h _ =>
        Finset.sum_congr rfl (fun h' _ => hsplit h h'))).trans <|
      (Finset.sum_congr rfl (fun h _ => Finset.sum_comm)).trans Finset.sum_comm
  -- ------------------------------------------------------------------
  -- Step 2: the scaling identity
  -- ------------------------------------------------------------------
  have hscal : ∀ r ∈ Finset.range c.natAbs,
      BoxNorm.boxScaling t (fun i : Fin t => arithIcc (c * q i) L) (symIcc N)
        = ((((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card : ℝ)
              / (((symIcc N).card : ℝ)))
            * BoxNorm.boxScaling t (fun i : Fin t => arithIcc (q i) L)
                ((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))) := by
    intro r hr
    have hSr : ((((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card : ℝ)) ≠ 0 := by
      have h : 0 < ((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card :=
        card_filter_symIcc_mod_pos hc hcN (Finset.mem_range.mp hr)
      exact_mod_cast ne_of_gt h
    have hS : ((((symIcc N).card : ℝ))) ≠ 0 := by
      have h : 0 < (symIcc N).card := Finset.card_pos.mpr ⟨0, by
        rw [symIcc, Finset.mem_Icc]
        constructor <;> simp⟩
      exact_mod_cast ne_of_gt h
    rw [BoxNorm.boxScaling, BoxNorm.boxScaling]
    -- the two products of direction-set cardinalities agree
    have hprod : (∏ i : Fin t, (((arithIcc (c * q i) L).card : ℝ))⁻¹)
        = ∏ i : Fin t, (((arithIcc (q i) L).card : ℝ))⁻¹ :=
      Finset.prod_congr rfl (fun i _ => by rw [hcard i])
    rw [hprod, div_eq_mul_inv]
    field_simp
  -- ------------------------------------------------------------------
  -- Step 3: the complex identity for `boxSumPow`
  -- ------------------------------------------------------------------
  have hbox : boxSumPow t (fun i : Fin t => arithIcc (c * q i) L) (symIcc N) f
      = ∑ r ∈ Finset.range c.natAbs,
          ((((((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card : ℝ)
              / (((symIcc N).card : ℝ)) : ℝ) : ℂ)
            * boxSumPow t (fun i : Fin t => arithIcc (q i) L)
                ((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ)))
                (fun ξ : ℤ => f ((r : ℤ) + c * ξ))) := by
    rw [BoxNorm.boxSumPow_eq_scaling t (fun i : Fin t => arithIcc (c * q i) L) (symIcc N) f,
      hraw, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [BoxNorm.boxSumPow_eq_scaling t (fun i : Fin t => arithIcc (q i) L)
        ((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ)))
        (fun ξ : ℤ => f ((r : ℤ) + c * ξ)), hscal r hr]
    push_cast
    ring
  -- ------------------------------------------------------------------
  -- Step 4: taking norms
  -- ------------------------------------------------------------------
  have hdilsupp : ∀ r : ℕ, FinSuppZ (fun ξ : ℤ => f ((r : ℤ) + c * ξ)) := by
    intro r
    refine ⟨M + r, fun ξ hξ => ?_⟩
    apply hM
    have h1 : (c * ξ).natAbs ≤ ((r : ℤ) + c * ξ).natAbs + r := by
      have h := Int.natAbs_add_le ((r : ℤ) + c * ξ) (-(r : ℤ))
      rw [Int.natAbs_neg] at h
      have h2 : (r : ℤ) + c * ξ + -(r : ℤ) = c * ξ := by ring
      rw [h2] at h
      simpa using h
    rw [Int.natAbs_mul] at h1
    have h2 : ξ.natAbs ≤ c.natAbs * ξ.natAbs :=
      Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hcne)
    omega
  have hmain : boxSumPow t (fun i : Fin t => arithIcc (c * q i) L) (symIcc N) f
      = (((∑ r ∈ Finset.range c.natAbs,
            ((((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card : ℝ)
                / (((symIcc N).card : ℝ)))
              * boxNormPow t (fun i : Fin t => arithIcc (q i) L)
                  ((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ)))
                  (fun ξ : ℤ => f ((r : ℤ) + c * ξ))) : ℝ) : ℂ) := by
    rw [hbox, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [BoxNorm.boxSumPow_eq_boxNormPow ht (hdilsupp r), ← Complex.ofReal_mul]
  have hnn : (0 : ℝ) ≤ ∑ r ∈ Finset.range c.natAbs,
      ((((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card : ℝ)
          / (((symIcc N).card : ℝ)))
        * boxNormPow t (fun i : Fin t => arithIcc (q i) L)
            ((symIcc N).filter (fun x : ℤ => x % c = (r : ℤ)))
            (fun ξ : ℤ => f ((r : ℤ) + c * ξ)) :=
    Finset.sum_nonneg (fun r _ => mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (norm_nonneg _))
  rw [show boxNormPow t (fun i : Fin t => arithIcc (c * q i) L) (symIcc N) f
        = ‖boxSumPow t (fun i : Fin t => arithIcc (c * q i) L) (symIcc N) f‖ from rfl,
      hmain, Complex.norm_of_nonneg hnn]

end

end Work.Peluse.LadderP
