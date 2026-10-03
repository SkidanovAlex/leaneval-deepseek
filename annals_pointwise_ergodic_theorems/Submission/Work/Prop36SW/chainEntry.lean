import Mathlib
import Submission.Work.Prop36SW.badSetDensity
import Submission.Work.Peluse.Prop36SW.spreadBack
import Submission.Work.Prop36SW.dirBound
import Submission.Work.Peluse.Prop36SW.initialState
import Submission.Work.Prop36SW.famAvg_window_ratio_le
import Submission.Work.Peluse.Prop36SW.lstatePeelFin

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-!
# `Work.Prop36SW.chainEntry`

The entry point of the §5 chain: from the family average `η ≤ D.famAvg (d'+2) H c N f`
(Proposition 3.4's output) produce an `LStateBox` state, i.e. a lower bound on the *rectangular*
average of the level-`|I_{d'+1}|` box norms with the slot coefficients `|slotCoeff|`, at the
direction window `H+1` and at some ambient window `N₁ ≥ N`.

The mathematical content is `initialStateBox` below, which is `initialState`/`initialState_gen` with
the "good set" restriction **removed**: `LStateBox` does not demand the non-vanishing of the
coefficients, so the state may live on the full parameter box `Abox D (d'+1) H` — the bad-set
density hypothesis of `initialState` is then unnecessary (the average over the full box dominates
the average over any subset, since the box norms are nonnegative).  This is what makes the statement
independent of whether `c = 0` (in which case every slot coefficient vanishes).

`chainEntry` adds the ambient-window bookkeeping: the `LStateBox` side condition
`|p| (H+1) (H+1) ≤ N₁` forces `N₁ ≳ |c| d'! (H+1)^d'`, which is `≲ N` by the scale hypothesis
`(H+1)^{d'+2} ≤ A₀ N`; the family average is transported from the window `N` to `N₁` by the
(proved) window monotonicity `famAvg_window_ratio_le`, at the cost of the datum-only constant `Cw`.
-/

open Work.Peluse.Prop36SW

/-- **The entry state of the §5 chain, on the full parameter box.**

From the family average `η ≤ D.famAvg (d'+2) H c N f` and the coefficient bound
`|slotCoeff| (H+1) (H+1) ≤ N` on the closed box `D.parBox (d'+1) H`, the *full* rectangular average
of the level-`|I_{d'+1}|` box norms with the absolute slot coefficients at the direction window
`H+1` dominates `η / 2 ^ (1 + 2 |I_{d'+1}|)`.

This is `Work.Peluse.Prop36SW.initialState_gen` with the parameter set enlarged from the good set to
the whole flat box `Abox D (d'+1) H`. -/
theorem initialStateBox (D : Work.Peluse.UControl.IdxDatum) (d' : ℕ) (c : ℤ) (N H : ℕ)
    (f : ℤ → ℂ) (η : ℝ)
    (hH : 1 ≤ H) (hN : 1 ≤ N) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsu : Work.Peluse.SupportIn f N)
    (hI : 2 ≤ Fintype.card (D.I (d' + 1)))
    (hfam : η ≤ D.famAvg (d' + 2) H c N f)
    (hbound : ∀ s : D.S (d' + 1), ∀ a ∈ D.parBox (d' + 1) H,
      |Work.Peluse.slotCoeff D (d' + 2) c d' s (D.pad (d' + 1) a)| * ((H : ℤ) + 1) * ((H : ℤ) + 1) ≤ (N : ℤ))
    (hbox : ((H : ℝ) + 1) * ((H : ℝ) + 1) ≤ (N : ℝ)) :
    Work.Peluse.Prop36SW.LStateBox
      (kω := fun _ : Work.Peluse.UControl.SlotSet (D.S (d' + 1)) (fun _ => 1) => 1)
      (p := fun (s : D.S (d' + 1)) (x : Fin (Work.Peluse.Prop36SW.nD D (d' + 1)) → ℤ) =>
        |Work.Peluse.slotCoeff D (d' + 2) c d' s (D.pad (d' + 1) (Work.Peluse.Prop36SW.decD D (d' + 1) x))|)
      (H + 1) (H + 1) N 1 (Work.Peluse.Prop36SW.Abox D (d' + 1) H) (fun _ => f)
      (η / 2 ^ (1 + (2 : ℕ) * Fintype.card (D.I (d' + 1)))) := by
  classical
  set cc : Finset (D.Idx (d' + 1)) := D.parBox (d' + 1) H with hcc
  set Pt : Finset (D.S (d' + 1) → ℤ) :=
    Fintype.piFinset (fun _ : D.S (d' + 1) => Finset.Icc (-(H : ℤ)) (H : ℤ)) with hPt
  set Pb : Finset (Slot (D.S (d' + 1)) (fun _ => 1) → ℤ) :=
    paramBox (k := fun _ : D.S (d' + 1) => 1) (H + 1) with hPb
  set koef : D.S (d' + 1) → D.Idx (d' + 1) → ℤ :=
    fun s a => Work.Peluse.slotCoeff D (d' + 2) c d' s (D.pad (d' + 1) a) with hkoef
  set Phi : D.Idx (d' + 1) → (D.S (d' + 1) → ℤ) → ℝ := fun a s =>
      Work.Peluse.boxNorm (Fintype.card (D.I (d' + 1)))
        (fun i => Work.Peluse.arithIcc (D.dir (d' + 2) c (d' + 1)
          ((Fintype.equivFin (D.I (d' + 1))).symm i) (Work.Peluse.padUpdate D d' a s)) H)
        (Work.Peluse.symIcc N) f with hPhi
  set F : D.Idx (d' + 1) → ℝ := fun a => (Pt.card : ℝ)⁻¹ * ∑ s ∈ Pt, Phi a s with hF
  set Cf : ℝ := ((4 : ℝ) ^ (Fintype.card (FamIdx (k := fun _ : D.S (d' + 1) => 1) (fun _ => 1)))) ^
      (1 / (2 : ℝ) ^ (Fintype.card (FamIdx (k := fun _ : D.S (d' + 1) => 1) (fun _ => 1)))) with hCf
  set Gg : D.Idx (d' + 1) → (Slot (D.S (d' + 1)) (fun _ => 1) → ℤ) → ℝ := fun a b =>
      Work.Peluse.boxNorm (Fintype.card (FamIdx (k := fun _ : D.S (d' + 1) => 1) (fun _ => 1)))
        (fun j => pDirFamG (p := fun s (a' : D.Idx (d' + 1)) => |koef s a'|) (H + 1) a b
          ((Fintype.equivFin (FamIdx (k := fun _ : D.S (d' + 1) => 1) (fun _ => 1))).symm j))
        (Work.Peluse.symIcc N) f with hGg
  set Gflat : (Fin (Work.Peluse.Prop36SW.nD D (d' + 1)) → ℤ) →
      (Slot (D.S (d' + 1)) (fun _ => 1) → ℤ) → ℝ := fun x b =>
      Work.Peluse.boxNorm (Fintype.card (FamIdx (k := fun _ : D.S (d' + 1) => 1) (fun _ => 1)))
        (fun j => pDirFamG
          (p := fun s (x' : Fin (Work.Peluse.Prop36SW.nD D (d' + 1)) → ℤ) =>
            |koef s (Work.Peluse.Prop36SW.decD D (d' + 1) x')|) (H + 1) x b
          ((Fintype.equivFin (FamIdx (k := fun _ : D.S (d' + 1) => 1) (fun _ => 1))).symm j))
        (Work.Peluse.symIcc N) f with hGflat
  -- ## elementary consequences of the hypotheses
  have hfin : Work.Peluse.FinSuppZ f := Work.Peluse.FinSuppZ.of_supportIn hsu
  have ht : 2 ≤ Fintype.card (FamIdx (k := fun _ : D.S (d' + 1) => 1) (fun _ => 1)) := by
    rw [Work.Peluse.card_famIdx_eq_cardI D (d' + 1)]
    exact hI
  -- ## the family average rewritten as an average over `Pt`
  have hfamA : η ≤ (cc.card : ℝ)⁻¹ * ∑ a ∈ cc, F a := by
    simp only [hcc, hF, hPt, hPhi]
    refine le_trans hfam ?_
    have h := parBoxSuccAverage D d' H (fun u => Work.Peluse.boxNorm (Fintype.card (D.I (d' + 1)))
      (fun i => Work.Peluse.arithIcc (D.dir (d' + 2) c (d' + 1)
        ((Fintype.equivFin (D.I (d' + 1))).symm i) u) H) (Work.Peluse.symIcc N) f)
    simp only [IdxDatum.famAvg, IdxDatum.famNorm] at h ⊢
    exact le_of_eq h
  -- ## the pointwise scalar bound
  have hPhi_le_one : ∀ a ∈ cc, ∀ s ∈ Pt, Phi a s ≤ 1 := by
    intro a ha s hs
    rw [hPhi]
    exact boxNorm_le_one_of_supportIn hf hsu
  have hF_le_one : ∀ a ∈ cc, F a ≤ 1 := by
    intro a ha
    have hPtne : Pt.Nonempty := by
      refine ⟨fun _ => 0, ?_⟩
      rw [hPt, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hcard : (0 : ℝ) < (Pt.card : ℝ) := by
      have h := Finset.card_pos.mpr hPtne
      exact_mod_cast h
    have hsum : ∑ s ∈ Pt, Phi a s ≤ (Pt.card : ℝ) := by
      calc ∑ s ∈ Pt, Phi a s ≤ ∑ _s ∈ Pt, (1 : ℝ) :=
            Finset.sum_le_sum (fun s hs => hPhi_le_one a ha s hs)
        _ = (Pt.card : ℝ) := by simp
    rw [hF]
    calc (Pt.card : ℝ)⁻¹ * ∑ s ∈ Pt, Phi a s ≤ (Pt.card : ℝ)⁻¹ * (Pt.card : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hcard)
  have hF_nn : ∀ a ∈ cc, 0 ≤ F a := by
    intro a ha
    rw [hF]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => ?_))
    rw [hPhi]
    exact Real.rpow_nonneg (norm_nonneg _) _
  -- ## the pointwise comparison (the `coreCompare` input)
  have hcore : ∀ a ∈ cc, F a ≤ Cf * ((Pb.card : ℝ)⁻¹ * ∑ b ∈ Pb, Gg a b) := by
    intro a ha
    have hcore' := coreCompare (p := koef) H hH a (Work.Peluse.symIcc N) hfin ht
    have hsum_eq : (∑ s ∈ Fintype.piFinset (fun _ : D.S (d' + 1) => Finset.Icc (-(H : ℤ)) (H : ℤ)), Phi a s)
        = ∑ s ∈ Fintype.piFinset (fun _ : D.S (d' + 1) => Finset.Icc (-(H : ℤ)) (H : ℤ)),
            Work.Peluse.boxNorm (Fintype.card (FamIdx (k := fun _ : D.S (d' + 1) => 1) (fun _ => 1)))
              (fun j => pDirFam (p := fun s (_ : Fin 0 → ℤ) => koef s a) H (fun _ => (0 : ℤ))
                (fun k => s k.1)
                ((Fintype.equivFin (FamIdx (k := fun _ : D.S (d' + 1) => 1) (fun _ => 1))).symm j))
              (Work.Peluse.symIcc N) f := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [hPhi]
      exact famNorm_eq_pDirFam D (d' + 2) c d' H N f a s
    rw [hF, hPt, hCf, hPb, hGg]
    simp only []
    refine le_trans (le_of_eq ?_) hcore'
    rw [hsum_eq]
  -- ## the final constant
  have hCpos : 0 < Cf := by
    rw [hCf]
    positivity
  have hCbound : Cf * ((4 : ℝ) ^ (Fintype.card (D.I (d' + 1))))⁻¹ ≤ 1 := by
    have hCfv : Cf ≤ (4 : ℝ) ^ (Fintype.card (D.I (d' + 1))) := by
      rw [hCf, Work.Peluse.card_famIdx_eq_cardI D (d' + 1)]
      refine Real.rpow_le_self_of_one_le ?_ ?_
      · exact one_le_pow₀ (by norm_num)
      · rw [div_le_one (by positivity)]
        exact one_le_pow₀ (by norm_num)
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ (Fintype.card (D.I (d' + 1))) := by positivity
    calc Cf * ((4 : ℝ) ^ (Fintype.card (D.I (d' + 1))))⁻¹
        ≤ (4 : ℝ) ^ (Fintype.card (D.I (d' + 1))) *
            ((4 : ℝ) ^ (Fintype.card (D.I (d' + 1))))⁻¹ :=
          mul_le_mul_of_nonneg_right hCfv (by positivity)
      _ = 1 := mul_inv_cancel₀ (ne_of_gt h4pos)
  -- ## the assembly over the full closed box
  have hgoodtriv : 4 * ((cc \ cc).card : ℝ) ≤ η * (cc.card : ℝ) := by
    rw [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact mul_nonneg (le_of_lt hη0) (Nat.cast_nonneg _)
  have hbig : η / 2 ^ (1 + 2 * Fintype.card (D.I (d' + 1))) ≤
      (cc.card : ℝ)⁻¹ * (Pb.card : ℝ)⁻¹ * ∑ a ∈ cc, ∑ b ∈ Pb, Gg a b :=
    averageAssembly (cc := cc) (A := cc) (Pb := Pb) (F := F) (G := Gg) (η := η) (C := Cf)
      (Ncard := Fintype.card (D.I (d' + 1))) hCpos (le_refl cc) hF_nn hF_le_one hη1 hfamA
      hgoodtriv hcore hCbound
  -- ## transporting the average to the flat box `Abox D (d'+1) H`
  have hAbox : Abox D (d' + 1) H = cc.image (encD D (d' + 1)) := by
    rw [hcc]; rfl
  have hcardAb : (Abox D (d' + 1) H).card = cc.card := by
    rw [hAbox, Finset.card_image_of_injective _ (encD_injective D (d' + 1))]
  have hterm : ∀ a ∈ cc, ∀ b ∈ Pb,
      Gflat (encD D (d' + 1) a) b = Gg a b := by
    intro a ha b hb
    simp only [hGg, hGflat, pDirFamG, pDirG, decD_encD]
  have hsumflat : ∑ x ∈ Abox D (d' + 1) H, ∑ b ∈ Pb, Gflat x b
      = ∑ a ∈ cc, ∑ b ∈ Pb, Gg a b := by
    rw [hAbox, Finset.sum_image]
    · refine Finset.sum_congr rfl fun a ha => ?_
      exact Finset.sum_congr rfl fun b hb => hterm a ha b hb
    · intro x _ y _ hxy
      exact encD_injective D (d' + 1) hxy
  have hbig2 : η / 2 ^ (1 + (2 : ℕ) * Fintype.card (D.I (d' + 1))) ≤
      ((Abox D (d' + 1) H).card : ℝ)⁻¹ * (Pb.card : ℝ)⁻¹ *
        ∑ x ∈ Abox D (d' + 1) H, ∑ b ∈ Pb, Gflat x b := by
    rw [hsumflat, hcardAb]
    exact hbig
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · rw [div_le_one (by positivity)]
    exact le_trans hη1 (one_le_pow₀ (by norm_num))
  · omega
  · exact le_rfl
  · exact hN
  · simpa only [Nat.cast_add, Nat.cast_one] using hbox
  · intro i a ha
    have hb := hbound i (decD D (d' + 1) a) (decD_mem_parBox_of_mem_Abox ha)
    simpa only [Nat.cast_add, Nat.cast_one, abs_abs] using hb
  · intro i a ha
    have hb := hbound i (decD D (d' + 1) a) (decD_mem_parBox_of_mem_Abox ha)
    simpa only [Nat.cast_add, Nat.cast_one, abs_abs, one_mul] using hb
  · intro a ha x
    exact hf x
  · intro a ha
    exact hsu
  · simpa only [hGflat, hkoef, hPb] using hbig2

/-! ## Monotonicity of `LStateBox` in the strength `γ`

`γ` occurs in `LStateBox` only in the first two conjuncts and in the family bound, so any smaller
positive strength is also a valid state. -/
theorem LStateBox_mono {ι : Type} [Fintype ι] [DecidableEq ι]
    {kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ} {P : Type} [DecidableEq P]
    {p : ι → P → ℤ} {M₁ M₂ N Dc : ℕ} {A : Finset P} {g : P → ℤ → ℂ} {γ γ' : ℝ}
    (h : Work.Peluse.Prop36SW.LStateBox kω p M₁ M₂ N Dc A g γ') (hγ : γ ≤ γ') (hγ0 : 0 < γ) :
    Work.Peluse.Prop36SW.LStateBox kω p M₁ M₂ N Dc A g γ := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨hγ0, le_trans hγ h1, h2, h3, h4, h5, h6, h7, h8, h9, le_trans hγ h10⟩

/-- `|symIcc N| = 2N + 1`. -/
private lemma card_symIcc_local (N : ℕ) : (Work.Peluse.symIcc N).card = 2 * N + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by omega
  rw [h, Int.toNat_natCast]

end

end Work.Prop36SW
