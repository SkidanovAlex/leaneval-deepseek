import Mathlib
import Submission.Work.TMC13.PruferCore

/-!
# Continuity of the Prüfer core `pruferCore`

`Work.TMC13.pruferCore a r = 1 - r + (if r = 1 then π/2 else if r = 0 then -π/2
else arctan (tan (π (r - 1/2)) - a)) / π` is continuous on `univ ×ˢ [0,1]`.

On the open interior `r ∈ (0,1)` this is the arctan expression, while on the two boundary
lines `r = 0` and `r = 1` the explicit values `±π/2` are exactly the one-sided limits of
`arctan (tan (π (r - 1/2)) - a)` as `r → 0⁺` (respectively `r → 1⁻`), because
`tan (π (r - 1/2)) → -∞` (respectively `+∞`) there.  This is what makes the core continuous.
-/

namespace Work.TMC13

open Set Filter Topology

noncomputable section

/-- The arctangent part of the core, on the interior. -/
private def coreG (a r : ℝ) : ℝ :=
  Real.arctan (Real.tan (Real.pi * (r - 1 / 2)) - a)

/-- The interior expression for `pruferCore`. -/
private def coreExpr (a r : ℝ) : ℝ :=
  1 - r + coreG a r / Real.pi

private lemma Icc_zero_one_eq : Icc (0 : ℝ) 1 = {0} ∪ Ioo (0 : ℝ) 1 ∪ {1} := by
  ext x
  simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioo]
  constructor
  · rintro ⟨h0, h1⟩
    rcases eq_or_lt_of_le h0 with h | h
    · exact Or.inl (Or.inl h.symm)
    · rcases eq_or_lt_of_le h1 with h' | h'
      · exact Or.inr h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
  · rintro ((h | ⟨h0, h1⟩) | h)
    · subst h; exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨le_of_lt h0, le_of_lt h1⟩
    · subst h; exact ⟨zero_le_one, le_rfl⟩

private lemma pruferCore_eq_coreExpr {a r : ℝ} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    pruferCore a r = coreExpr a r := by
  simp only [pruferCore, coreExpr, coreG]
  rw [if_neg h1, if_neg h0]

/-! ### One-dimensional tangent limits -/

private lemma tendsto_tan_core_nhdsGT :
    Tendsto (fun r : ℝ => Real.tan (Real.pi * (r - 1 / 2))) (𝓝[>] (0 : ℝ)) atBot := by
  have hlin : Tendsto (fun r : ℝ => Real.pi * (r - 1 / 2)) (𝓝[>] (0 : ℝ))
      (𝓝[>] (-(Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous fun r : ℝ => Real.pi * (r - 1 / 2) := by fun_prop
      have h0 : Real.pi * ((0 : ℝ) - 1 / 2) = -(Real.pi / 2) := by ring
      simpa only [h0] using (hc.continuousAt (x := (0 : ℝ))).mono_left nhdsWithin_le_nhds
    · refine Filter.mem_of_superset (self_mem_nhdsWithin) ?_
      intro r hr
      have h : 0 < Real.pi * r := mul_pos Real.pi_pos (mem_Ioi.mp hr)
      have he : Real.pi * (r - 1 / 2) = Real.pi * r - Real.pi / 2 := by ring
      simp only [mem_ofPred_eq, mem_Ioi]
      rw [he]
      linarith
  exact Real.tendsto_tan_neg_pi_div_two.comp hlin

private lemma tendsto_tan_core_nhdsLT :
    Tendsto (fun r : ℝ => Real.tan (Real.pi * (r - 1 / 2))) (𝓝[<] (1 : ℝ)) atTop := by
  have hlin : Tendsto (fun r : ℝ => Real.pi * (r - 1 / 2)) (𝓝[<] (1 : ℝ))
      (𝓝[<] (Real.pi / 2)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous fun r : ℝ => Real.pi * (r - 1 / 2) := by fun_prop
      have h0 : Real.pi * ((1 : ℝ) - 1 / 2) = Real.pi / 2 := by ring
      simpa only [h0] using (hc.continuousAt (x := (1 : ℝ))).mono_left nhdsWithin_le_nhds
    · refine Filter.mem_of_superset (self_mem_nhdsWithin) ?_
      intro r hr
      have h : Real.pi * r < Real.pi := by
        simpa using mul_lt_mul_of_pos_left (mem_Iio.mp hr) Real.pi_pos
      have he : Real.pi * (r - 1 / 2) = Real.pi * r - Real.pi / 2 := by ring
      simp only [mem_ofPred_eq, mem_Iio]
      rw [he]
      linarith
  exact Real.tendsto_tan_pi_div_two.comp hlin

private lemma tendsto_snd_nhdsWithin_prod (x y : ℝ) (t : Set ℝ) :
    Tendsto Prod.snd (𝓝[(univ : Set ℝ) ×ˢ t] (x, y)) (𝓝[t] y) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · exact (continuous_snd.tendsto (x, y)).mono_left nhdsWithin_le_nhds
  · exact Filter.mem_of_superset self_mem_nhdsWithin (fun q hq => hq.2)

/-! ### Limits of `coreG` from the interior -/

private lemma tendsto_coreG_zero (a₀ : ℝ) :
    Tendsto (fun q : ℝ × ℝ => coreG q.1 q.2)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 0)) (𝓝 (-(Real.pi / 2))) := by
  have hB : (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) :=
    fun q hq => ⟨hq.1, hq.2.1⟩
  have hsnd : Tendsto Prod.snd (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 0))
      (𝓝[>] (0 : ℝ)) :=
    (tendsto_snd_nhdsWithin_prod a₀ 0 (Ioi (0 : ℝ))).mono_left (nhdsWithin_mono _ hB)
  have htan : Tendsto (fun q : ℝ × ℝ => Real.tan (Real.pi * (q.2 - 1 / 2)))
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 0)) atBot :=
    tendsto_tan_core_nhdsGT.comp hsnd
  have hneg : Tendsto (fun q : ℝ × ℝ => -q.1)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 0)) (𝓝 (-a₀)) :=
    (continuous_fst.neg.tendsto (a₀, 0)).mono_left nhdsWithin_le_nhds
  have hsum : Tendsto (fun q : ℝ × ℝ => Real.tan (Real.pi * (q.2 - 1 / 2)) - q.1)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 0)) atBot := by
    simpa only [sub_eq_add_neg] using htan.atBot_add hneg
  have harct : Tendsto
      (fun q : ℝ × ℝ => Real.arctan (Real.tan (Real.pi * (q.2 - 1 / 2)) - q.1))
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 0)) (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.comp hsum).mono_right nhdsWithin_le_nhds
  exact harct

private lemma tendsto_coreG_one (a₀ : ℝ) :
    Tendsto (fun q : ℝ × ℝ => coreG q.1 q.2)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 1)) (𝓝 (Real.pi / 2)) := by
  have hB : (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Iio (1 : ℝ) :=
    fun q hq => ⟨hq.1, hq.2.2⟩
  have hsnd : Tendsto Prod.snd (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 1))
      (𝓝[<] (1 : ℝ)) :=
    (tendsto_snd_nhdsWithin_prod a₀ 1 (Iio (1 : ℝ))).mono_left (nhdsWithin_mono _ hB)
  have htan : Tendsto (fun q : ℝ × ℝ => Real.tan (Real.pi * (q.2 - 1 / 2)))
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 1)) atTop :=
    tendsto_tan_core_nhdsLT.comp hsnd
  have hneg : Tendsto (fun q : ℝ × ℝ => -q.1)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 1)) (𝓝 (-a₀)) :=
    (continuous_fst.neg.tendsto (a₀, 1)).mono_left nhdsWithin_le_nhds
  have hsum : Tendsto (fun q : ℝ × ℝ => Real.tan (Real.pi * (q.2 - 1 / 2)) - q.1)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 1)) atTop := by
    simpa only [sub_eq_add_neg] using htan.atTop_add hneg
  have harct : Tendsto
      (fun q : ℝ × ℝ => Real.arctan (Real.tan (Real.pi * (q.2 - 1 / 2)) - q.1))
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 1)) (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp hsum).mono_right nhdsWithin_le_nhds
  exact harct

private lemma tendsto_coreExpr_zero (a₀ : ℝ) :
    Tendsto (fun q : ℝ × ℝ => coreExpr q.1 q.2)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 0)) (𝓝 (1 / 2)) := by
  have hG : Tendsto (fun q : ℝ × ℝ => coreG q.1 q.2 / Real.pi)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 0)) (𝓝 (-(1 / 2))) := by
    have hval : -(Real.pi / 2) / Real.pi = -(1 / 2) := by
      rw [div_eq_iff (ne_of_gt Real.pi_pos)]; ring
    simpa only [hval] using (tendsto_coreG_zero a₀).div_const Real.pi
  have hone : Tendsto (fun q : ℝ × ℝ => (1 : ℝ) - q.2)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 0)) (𝓝 (1 : ℝ)) := by
    have h : Continuous fun q : ℝ × ℝ => (1 : ℝ) - q.2 := by fun_prop
    simpa using (h.tendsto (a₀, (0 : ℝ))).mono_left nhdsWithin_le_nhds
  have hsum := hone.add hG
  have hval : (1 : ℝ) + -(1 / 2) = 1 / 2 := by norm_num
  rw [hval] at hsum
  exact hsum

private lemma tendsto_coreExpr_one (a₀ : ℝ) :
    Tendsto (fun q : ℝ × ℝ => coreExpr q.1 q.2)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 1)) (𝓝 (1 / 2)) := by
  have hG : Tendsto (fun q : ℝ × ℝ => coreG q.1 q.2 / Real.pi)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 1)) (𝓝 (1 / 2)) := by
    have hval : Real.pi / 2 / Real.pi = 1 / 2 := by
      rw [div_eq_iff (ne_of_gt Real.pi_pos)]; ring
    simpa only [hval] using (tendsto_coreG_one a₀).div_const Real.pi
  have hone : Tendsto (fun q : ℝ × ℝ => (1 : ℝ) - q.2)
      (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] (a₀, 1)) (𝓝 (0 : ℝ)) := by
    have h : Continuous fun q : ℝ × ℝ => (1 : ℝ) - q.2 := by fun_prop
    simpa using (h.tendsto (a₀, (1 : ℝ))).mono_left nhdsWithin_le_nhds
  have hsum := hone.add hG
  have hval : (0 : ℝ) + 1 / 2 = 1 / 2 := by norm_num
  rw [hval] at hsum
  exact hsum

/-! ### Gluing the three pieces -/

private lemma tendsto_nhdsWithin_Icc_of_parts {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {v : ℝ}
    (hA : Tendsto f (𝓝[(univ : Set ℝ) ×ˢ ({0} : Set ℝ)] p) (𝓝 v))
    (hB : Tendsto f (𝓝[(univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1] p) (𝓝 v))
    (hC : Tendsto f (𝓝[(univ : Set ℝ) ×ˢ ({1} : Set ℝ)] p) (𝓝 v)) :
    Tendsto f (𝓝[(univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1] p) (𝓝 v) := by
  have hs : (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1
      = ((univ : Set ℝ) ×ˢ ({0} : Set ℝ) ∪ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1)
        ∪ (univ : Set ℝ) ×ˢ ({1} : Set ℝ) := by
    rw [Icc_zero_one_eq, Set.prod_union, Set.prod_union]
  simp only [hs, nhdsWithin_union, Filter.tendsto_sup]
  exact ⟨⟨hA, hB⟩, hC⟩

end

theorem pruferCore_continuous :
    ContinuousOn (Function.uncurry Work.TMC13.pruferCore) (Set.univ ×ˢ Set.Icc 0 1) := by
  intro p hp
  simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc] at hp
  obtain ⟨h0, h1⟩ := hp
  rcases lt_or_eq_of_le h0 with h0lt | h0eq
  · rcases lt_or_eq_of_le h1 with h1lt | h1eq
    · -- interior: 0 < p.2 < 1
      have hT : {q : ℝ × ℝ | q.2 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 p :=
        (isOpen_Ioo.preimage continuous_snd).mem_nhds ⟨h0lt, h1lt⟩
      have hfc : (fun q : ℝ × ℝ => coreExpr q.1 q.2) =ᶠ[𝓝 p]
          (fun q : ℝ × ℝ => pruferCore q.1 q.2) := by
        refine Filter.mem_of_superset hT ?_
        intro q hq
        have hq0 : q.2 ≠ 0 := ne_of_gt hq.1
        have hq1 : q.2 ≠ 1 := ne_of_lt hq.2
        exact (pruferCore_eq_coreExpr hq0 hq1).symm
      have hcore : ContinuousAt (fun q : ℝ × ℝ => coreExpr q.1 q.2) p := by
        have hG : ContinuousAt (fun q : ℝ × ℝ => coreG q.1 q.2) p := by
          have hlin : ContinuousAt (fun q : ℝ × ℝ => Real.pi * (q.2 - 1 / 2)) p := by
            fun_prop
          have hcos : Real.cos (Real.pi * (p.2 - 1 / 2)) ≠ 0 := by
            have hmem : Real.pi * (p.2 - 1 / 2) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
              ⟨by nlinarith [Real.pi_pos, h0lt, h1lt],
                by nlinarith [Real.pi_pos, h0lt, h1lt]⟩
            exact (Real.cos_pos_of_mem_Ioo hmem).ne'
          have htan : ContinuousAt (fun q : ℝ × ℝ => Real.tan (Real.pi * (q.2 - 1 / 2))) p :=
            ContinuousAt.comp (f := fun q : ℝ × ℝ => Real.pi * (q.2 - 1 / 2)) (x := p)
              (Real.continuousAt_tan.mpr hcos) hlin
          have hsub : ContinuousAt
              (fun q : ℝ × ℝ => Real.tan (Real.pi * (q.2 - 1 / 2)) - q.1) p :=
            htan.sub continuous_fst.continuousAt
          exact ContinuousAt.comp
            (f := fun q : ℝ × ℝ => Real.tan (Real.pi * (q.2 - 1 / 2)) - q.1) (x := p)
            (Real.continuous_arctan.continuousAt) hsub
        have hmain : ContinuousAt
            (fun q : ℝ × ℝ => 1 - q.2 + coreG q.1 q.2 / Real.pi) p :=
          (continuousAt_const.sub continuous_snd.continuousAt).add (hG.div_const Real.pi)
        exact hmain
      exact (hcore.congr hfc).continuousWithinAt
    · -- right boundary: p.2 = 1
      have hval : pruferCore p.1 p.2 = 1 / 2 := by
        rw [h1eq]; exact pruferCore_one p.1
      have hpe : p = (p.1, 1) := by rw [← h1eq]
      change Tendsto (fun q : ℝ × ℝ => pruferCore q.1 q.2)
        (𝓝[(univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1] p) (𝓝 (pruferCore p.1 p.2))
      rw [hval, hpe]
      refine tendsto_nhdsWithin_Icc_of_parts ?_ ?_ ?_
      · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        refine Filter.mem_of_superset self_mem_nhdsWithin ?_
        intro q hq
        have hq2 : q.2 = 0 := by simpa using hq.2
        show (1 / 2 : ℝ) = pruferCore q.1 q.2
        rw [hq2, pruferCore_zero]
      · refine Filter.Tendsto.congr' ?_ (tendsto_coreExpr_one p.1)
        refine Filter.mem_of_superset self_mem_nhdsWithin ?_
        intro q hq
        have hq0 : q.2 ≠ 0 := ne_of_gt hq.2.1
        have hq1 : q.2 ≠ 1 := ne_of_lt hq.2.2
        exact (pruferCore_eq_coreExpr hq0 hq1).symm
      · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        refine Filter.mem_of_superset self_mem_nhdsWithin ?_
        intro q hq
        have hq2 : q.2 = 1 := by simpa using hq.2
        show (1 / 2 : ℝ) = pruferCore q.1 q.2
        rw [hq2]
        exact (pruferCore_one q.1).symm
  · -- left boundary: p.2 = 0
    have hval : pruferCore p.1 p.2 = 1 / 2 := by
      rw [h0eq.symm]; exact pruferCore_zero p.1
    have hpe : p = (p.1, 0) := by rw [h0eq]
    change Tendsto (fun q : ℝ × ℝ => pruferCore q.1 q.2)
      (𝓝[(univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1] p) (𝓝 (pruferCore p.1 p.2))
    rw [hval, hpe]
    refine tendsto_nhdsWithin_Icc_of_parts ?_ ?_ ?_
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro q hq
      have hq2 : q.2 = 0 := by simpa using hq.2
      show (1 / 2 : ℝ) = pruferCore q.1 q.2
      rw [hq2, pruferCore_zero]
    · refine Filter.Tendsto.congr' ?_ (tendsto_coreExpr_zero p.1)
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro q hq
      have hq0 : q.2 ≠ 0 := ne_of_gt hq.2.1
      have hq1 : q.2 ≠ 1 := ne_of_lt hq.2.2
      exact (pruferCore_eq_coreExpr hq0 hq1).symm
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro q hq
      have hq2 : q.2 = 1 := by simpa using hq.2
      show (1 / 2 : ℝ) = pruferCore q.1 q.2
      rw [hq2]
      exact (pruferCore_one q.1).symm

end Work.TMC13
