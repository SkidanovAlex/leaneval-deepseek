import Mathlib

namespace Work.HornSC

open Filter
open scoped Topology

noncomputable section

/-! ### Auxiliary reparametrisation of `[-1,1]`

`clip1` clips a real number to `[-1,1]` and `reparam a c` sends `[-1,1]` affinely onto `[a,c]`
(with `-1 ↦ c` and `1 ↦ a`), extending constantly outside. -/

/-- Clipping of `ℝ` to the interval `[-1,1]`. -/
def clip1 (t : ℝ) : ℝ := max (-1) (min 1 t)

lemma clip1_le_one (t : ℝ) : clip1 t ≤ 1 := max_le (by norm_num) (min_le_left 1 t)

lemma clip1_ge_neg_one (t : ℝ) : -1 ≤ clip1 t := le_max_left (-1) (min 1 t)

lemma continuous_clip1 : Continuous clip1 :=
  continuous_const.max (continuous_const.min continuous_id)

lemma clip1_neg_one : clip1 (-1) = -1 := by norm_num [clip1]

lemma clip1_one : clip1 1 = 1 := by norm_num [clip1]

lemma clip1_eq_self {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) : clip1 t = t := by
  simp only [clip1, min_eq_right ht.2, max_eq_right ht.1]

/-- The affine reparametrisation of `[-1,1]` onto `[a,c]`, extended constantly outside. -/
def reparam (a c t : ℝ) : ℝ := a + (c - a) * (1 - clip1 t) / 2

lemma continuous_reparam (a c : ℝ) : Continuous (reparam a c) := by
  change Continuous fun t => a + (c - a) * (1 - clip1 t) / 2
  exact Continuous.add continuous_const (Continuous.div_const
    (Continuous.mul continuous_const (Continuous.sub continuous_const continuous_clip1)) 2)

lemma reparam_neg_one (a c : ℝ) : reparam a c (-1) = c := by
  simp only [reparam, clip1_neg_one]; ring

lemma reparam_one (a c : ℝ) : reparam a c 1 = a := by
  simp only [reparam, clip1_one]; ring

lemma reparam_mem {a c : ℝ} (hac : a ≤ c) (t : ℝ) : reparam a c t ∈ Set.Icc a c := by
  have hca : 0 ≤ c - a := by linarith
  have hs0 : 0 ≤ (1 - clip1 t) / 2 := by linarith [clip1_le_one t]
  have hs1 : (1 - clip1 t) / 2 ≤ 1 := by linarith [clip1_ge_neg_one t]
  simp only [reparam]
  constructor
  · have h := mul_nonneg hca hs0; linarith
  · have h := mul_le_mul_of_nonneg_left hs1 hca; linarith

/-! ### The strip-crossing sub-interval of a real function -/

/-- A continuous `f : ℝ → ℝ` with `f 0 > η` and `f 1 < -η` has a sub-interval `[a,c] ⊆ [0,1]`
on which it runs from level `η` down to level `-η`, without ever leaving the strip `|f| ≤ η`. -/
theorem strip_interval {f : ℝ → ℝ} (hf : Continuous f) {η : ℝ} (hη : 0 ≤ η)
    (h0 : η < f 0) (h1 : f 1 < -η) :
    ∃ a c : ℝ, 0 ≤ a ∧ a ≤ c ∧ c ≤ 1 ∧ f a = η ∧ f c = -η ∧
      ∀ t ∈ Set.Icc a c, |f t| ≤ η := by
  -- `C` = the set of times at which `f` has already reached level `-η`; `c` is its first entry.
  set C : Set ℝ := Set.Icc (0:ℝ) 1 ∩ {t : ℝ | f t ≤ -η} with hCdef
  have hCmem : ∀ t : ℝ, t ∈ C ↔ t ∈ Set.Icc (0:ℝ) 1 ∧ f t ≤ -η := by
    intro t
    rw [hCdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
  have hCcl : IsClosed C := by
    rw [hCdef]
    exact isClosed_Icc.inter (isClosed_le hf continuous_const)
  have hCne : C.Nonempty := ⟨1, (hCmem 1).2 ⟨⟨zero_le_one, le_refl 1⟩, le_of_lt h1⟩⟩
  have hCbdd : BddBelow C := ⟨0, fun t ht => ((hCmem t).1 ht).1.1⟩
  set c : ℝ := sInf C with hceq
  have hcC : c ∈ C := by rw [hceq]; exact hCcl.csInf_mem hCne hCbdd
  have hc01 : c ∈ Set.Icc (0:ℝ) 1 := ((hCmem c).1 hcC).1
  have hcf : f c ≤ -η := ((hCmem c).1 hcC).2
  have hcf_eq : f c = -η := by
    by_contra hne
    have hlt : f c < -η := lt_of_le_of_ne hcf hne
    have hcne0 : c ≠ 0 := by
      intro h
      rw [h] at hcf
      linarith
    have hcpos : 0 < c := lt_of_le_of_ne hc01.1 (Ne.symm hcne0)
    have hnear : {t : ℝ | f t < -η} ∈ 𝓝 c :=
      ContinuousAt.eventually_lt hf.continuousAt continuousAt_const hlt
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
    set δ' : ℝ := min δ c with hδ'def
    have hδ'pos : 0 < δ' := lt_min hδpos hcpos
    have hδ'le : δ' ≤ δ := min_le_left δ c
    have hδ'lec : δ' ≤ c := min_le_right δ c
    set t : ℝ := c - δ' / 2 with htdef
    have htlt : t < c := by rw [htdef]; linarith
    have htge : 0 ≤ t := by rw [htdef]; linarith
    have htle1 : t ≤ 1 := by linarith [hc01.2]
    have hdist : dist t c < δ := by
      have habs : |t - c| = δ' / 2 := by
        rw [htdef]
        have hrew : c - δ' / 2 - c = -(δ' / 2) := by ring
        rw [hrew, abs_neg, abs_of_nonneg (by linarith)]
      rw [Real.dist_eq, habs]
      linarith
    have hft : f t < -η := hδsub (by rw [Metric.mem_ball]; exact hdist)
    have hmem : t ∈ C := (hCmem t).2 ⟨⟨htge, htle1⟩, le_of_lt hft⟩
    have hle : sInf C ≤ t := csInf_le hCbdd hmem
    rw [← hceq] at hle
    linarith
  -- on `[0,c]` the function never goes below `-η` again
  have hlow : ∀ t ∈ Set.Icc (0:ℝ) c, -η ≤ f t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have ht1 : t ≤ 1 := le_trans ht.2 hc01.2
      have hnotC : ¬ (t ∈ C) := by
        intro htC
        have hle : sInf C ≤ t := csInf_le hCbdd htC
        rw [← hceq] at hle
        linarith
      have hnot : ¬ (f t ≤ -η) := fun h => hnotC ((hCmem t).2 ⟨⟨ht.1, ht1⟩, h⟩)
      linarith [not_le.mp hnot]
    · rw [heq, hcf_eq]
  -- `E` = the set of times in `[0,c]` at which `f` is at level `η`; `a` is its last element.
  set E : Set ℝ := Set.Icc (0:ℝ) c ∩ {t : ℝ | f t = η} with hEdef
  have hEmem : ∀ t : ℝ, t ∈ E ↔ t ∈ Set.Icc (0:ℝ) c ∧ f t = η := by
    intro t
    rw [hEdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
  have hEcl : IsClosed E := by
    rw [hEdef]
    exact isClosed_Icc.inter (isClosed_eq hf continuous_const)
  have hEne : E.Nonempty := by
    have hmem : η ∈ Set.Icc (f c) (f 0) := ⟨by linarith [hcf_eq], le_of_lt h0⟩
    obtain ⟨u, hu, hfu⟩ :=
      (intermediate_value_Icc' (a := (0:ℝ)) (b := c) hc01.1 hf.continuousOn) hmem
    exact ⟨u, (hEmem u).2 ⟨hu, hfu⟩⟩
  have hEbdd : BddAbove E := ⟨c, fun t ht => ((hEmem t).1 ht).1.2⟩
  set a : ℝ := sSup E with haeq
  have haE : a ∈ E := by rw [haeq]; exact hEcl.csSup_mem hEne hEbdd
  have ha0 : 0 ≤ a := ((hEmem a).1 haE).1.1
  have hac : a ≤ c := ((hEmem a).1 haE).1.2
  have haf : f a = η := ((hEmem a).1 haE).2
  have hsup : ∀ t ∈ E, t ≤ a := by
    intro t ht
    rw [haeq]
    exact le_csSup hEbdd ht
  have hup : ∀ t ∈ Set.Icc a c, f t ≤ η := by
    intro t ht
    by_contra hcon
    have hgt : η < f t := not_le.mp hcon
    have hmem : η ∈ Set.Icc (f c) (f t) := ⟨by linarith [hcf_eq], le_of_lt hgt⟩
    obtain ⟨s, hs, hfs⟩ :=
      (intermediate_value_Icc' (a := t) (b := c) ht.2 hf.continuousOn) hmem
    have hsE : s ∈ E := (hEmem s).2 ⟨⟨le_trans (le_trans ha0 ht.1) hs.1, hs.2⟩, hfs⟩
    have hsa : s ≤ a := hsup s hsE
    have has : a ≤ s := le_trans ht.1 hs.1
    have hta : t = a := le_antisymm (le_trans hs.1 hsa) ht.1
    have : f t = η := by rw [hta]; exact haf
    exact hcon (le_of_eq this)
  refine ⟨a, c, ha0, hac, hc01.2, haf, hcf_eq, fun t ht => ?_⟩
  rw [abs_le]
  exact ⟨hlow t ⟨le_trans ha0 ht.1, ht.2⟩, hup t ht⟩

/-! ### Extracting a strip-crossing path -/

/-- **Extracting a strip-crossing path from a path crossing the strip.** Given a continuous path
`γ : [0,1] → ℂ` starting above the line `Im = η` and ending below `Im = -η` (with `η ≥ 0`), there
is a continuous path `V : ℝ → ℂ` whose range lies in that of `γ`, which joins the level `Im = -η`
at time `-1` to the level `Im = η` at time `1`, and which stays inside the strip `|Im| ≤ η` with
bounded real part on `[-1,1]`. -/
theorem path_between_strip_sides {η : ℝ} (hη : 0 ≤ η)
    {γ : C(Set.Icc (0:ℝ) 1, ℂ)} (h0 : η < (γ 0).im) (h1 : (γ 1).im < -η) :
    ∃ (V : C(ℝ, ℂ)) (M : ℝ), 0 ≤ M ∧ (V (-1)).im = -η ∧ (V 1).im = η ∧
      (∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → |(V t).im| ≤ η ∧ |(V t).re| ≤ M) ∧
      Set.range V ⊆ Set.range γ := by
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  -- `F` is the imaginary part of `γ`, extended to all of `ℝ` by projecting onto `[0,1]`.
  let F : ℝ → ℝ := fun t => (γ (Set.projIcc (0:ℝ) 1 h01 t)).im
  have hFcont : Continuous F :=
    Complex.continuous_im.comp (γ.continuous.comp continuous_projIcc)
  have hFval : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1), F t = (γ ⟨t, ht⟩).im := by
    intro t ht
    show (γ (Set.projIcc (0:ℝ) 1 h01 t)).im = (γ ⟨t, ht⟩).im
    rw [Set.projIcc_of_mem h01 ht]
  have hsub0 : (⟨(0:ℝ), (Set.left_mem_Icc.mpr h01 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)⟩ : Set.Icc (0:ℝ) 1)
      = (0 : Set.Icc (0:ℝ) 1) := Subtype.ext rfl
  have hsub1 : (⟨(1:ℝ), (Set.right_mem_Icc.mpr h01 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)⟩ : Set.Icc (0:ℝ) 1)
      = (1 : Set.Icc (0:ℝ) 1) := Subtype.ext rfl
  have hF0 : η < F 0 := by
    rw [hFval 0 (Set.left_mem_Icc.mpr h01), hsub0]
    exact h0
  have hF1 : F 1 < -η := by
    rw [hFval 1 (Set.right_mem_Icc.mpr h01), hsub1]
    exact h1
  obtain ⟨a, c, ha0, hac, hc1, hFa, hFc, hbound⟩ := strip_interval hFcont hη hF0 hF1
  -- the reparametrised path
  have hucont : Continuous (reparam a c) := continuous_reparam a c
  have humem : ∀ t : ℝ, reparam a c t ∈ Set.Icc (0:ℝ) 1 := fun t =>
    ⟨le_trans ha0 (reparam_mem hac t).1, le_trans (reparam_mem hac t).2 hc1⟩
  let φ : C(ℝ, Set.Icc (0:ℝ) 1) :=
    ⟨fun t => ⟨reparam a c t, humem t⟩, Continuous.subtype_mk hucont humem⟩
  let V : C(ℝ, ℂ) := γ.comp φ
  have hVapp : ∀ t : ℝ, V t = γ ⟨reparam a c t, humem t⟩ :=
    fun t => ContinuousMap.comp_apply γ φ t
  have hc01 : c ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans ha0 hac, hc1⟩
  have ha01 : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha0, le_trans hac hc1⟩
  refine ⟨V, ‖γ‖, norm_nonneg γ, ?_, ?_, ?_, ?_⟩
  · have hsub : (⟨reparam a c (-1), humem (-1)⟩ : Set.Icc (0:ℝ) 1) = ⟨c, hc01⟩ :=
      Subtype.ext (reparam_neg_one a c)
    rw [hVapp, hsub, ← hFval c hc01]
    exact hFc
  · have hsub : (⟨reparam a c 1, humem 1⟩ : Set.Icc (0:ℝ) 1) = ⟨a, ha01⟩ :=
      Subtype.ext (reparam_one a c)
    rw [hVapp, hsub, ← hFval a ha01]
    exact hFa
  · intro t ht
    have hut : reparam a c t ∈ Set.Icc a c := reparam_mem hac t
    rw [hVapp t, ← hFval (reparam a c t) (humem t)]
    exact ⟨hbound (reparam a c t) hut,
      le_trans (Complex.abs_re_le_norm _) (ContinuousMap.norm_coe_le_norm γ ⟨reparam a c t, humem t⟩)⟩
  · intro w hw
    obtain ⟨t, rfl⟩ := hw
    exact ⟨φ t, (hVapp t).symm⟩

end

end Work.HornSC
