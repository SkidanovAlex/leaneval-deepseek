/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Splitting the Hölder norm across a radial cut

For `A = U × {a < ‖z‖ < d}`, `A₁ = U × {a < ‖z‖ < ρ}` and `A₂ = U × {ρ < ‖z‖ < d}`
(with `a < ρ < d`) we prove

  `holderNorm k α f A ≤ 2 * (holderNorm k α f A₁ + holderNorm k α f A₂)`

for every `f` that is `C^k` on the open annulus `A`.  The circle `‖z‖ = ρ` lies in the
interior of `A`, so `f` is smooth across it; the Hölder control on the two open halves
therefore extends to the whole annulus with a constant `2` independent of everything.

The proof reduces to two estimates at every derivative level `i ≤ k`:

* `iterDerivNorm i f A ≤ iterDerivNorm i f A₁ + iterDerivNorm i f A₂`
  (supremum over a dense subset, using that `A ⊆ closure (A₁ ∪ A₂)`),
* `holderSeminorm i α f A ≤ 2 * (holderSeminorm i α f A₁ + holderSeminorm i α f A₂)`.

The second one is the interesting one: for a pair `p ∈ A₁`, `q ∈ A₂` one intercalates the
point `r = (p.1, c)` on the circle `‖c‖ = ρ`; the Hölder bounds of the two halves extend
to `closure A₁` resp. `closure A₂` by continuity of `D^i f` on `A`, whence
`‖D^i f p - D^i f q‖ ≤ (s₁ + s₂)‖p - q‖^α`.
-/
import Mathlib
import Submission.Work.NN.DiscRadial.DiscRadialAux

noncomputable section
open scoped NNReal ENNReal ContDiff
open Set Filter Topology

namespace Work.NN.DiscRadial

open Work.CR.Flat

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The radial regions -/

/-- The open annulus `{a < ‖z‖ < d}` in `ℂ`. -/
def ann (a d : ℝ) : Set ℂ := {z : ℂ | a < ‖z‖ ∧ ‖z‖ < d}

/-- The product region `U × {a < ‖z‖ < d}`. -/
def reg (U : Set X) (a d : ℝ) : Set (X × ℂ) := U ×ˢ ann a d

@[simp] lemma isOpen_ann (a d : ℝ) : IsOpen (ann a d) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma isOpen_reg {U : Set X} (hU : IsOpen U) (a d : ℝ) : IsOpen (reg U a d) :=
  hU.prod (isOpen_ann a d)

lemma mem_reg_iff {U : Set X} {a d : ℝ} {p : X × ℂ} :
    p ∈ reg U a d ↔ p.1 ∈ U ∧ a < ‖p.2‖ ∧ ‖p.2‖ < d := Iff.rfl

@[simp] lemma norm_coe_real (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

/-! ## A supremum over a dense subset -/

/-- If `D ⊆ A ⊆ closure D` and `f` is continuous on `A`, then the supremum of `f` over `A`
is bounded by the supremum over `D`. -/
lemma iSup_le_iSup_of_subset_closure {E : Type*} [TopologicalSpace E] {β : Type*}
    [TopologicalSpace β] [CompleteLattice β] [ClosedIicTopology β] {A D : Set E} {f : E → β}
    (hf : ContinuousOn f A) (hDA : D ⊆ A) (hAD : A ⊆ closure D) :
    ⨆ x ∈ A, f x ≤ ⨆ x ∈ D, f x := by
  refine iSup_le fun x => iSup_le fun hx => ?_
  have hxD : x ∈ closure D := hAD hx
  haveI : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hxD
  have htend : Tendsto f (𝓝[D] x) (𝓝 (f x)) :=
    (hf.continuousWithinAt hx).mono_left (nhdsWithin_mono x hDA)
  have hev : ∀ᶠ y in 𝓝[D] x, f y ≤ ⨆ y ∈ D, f y :=
    Eventually.mono self_mem_nhdsWithin (fun y hy => le_iSup₂_of_le y hy le_rfl)
  exact le_of_tendsto htend hev

/-! ## Continuity of the iterated derivatives on an open set -/

lemma continuousOn_iteratedFDeriv_of_contDiffOn {k m : ℕ} {A : Set (X × ℂ)} (hA : IsOpen A)
    {f : X × ℂ → ℂ} (hf : ContDiffOn ℝ (k : WithTop ENat) f A) (hmk : m ≤ k) :
    ContinuousOn (iteratedFDeriv ℝ m f) A := by
  have h1 : ContinuousOn (iteratedFDerivWithin ℝ m f A) A :=
    hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hmk) hA.uniqueDiffOn
  refine h1.congr fun x hx => ?_
  exact (iteratedFDerivWithin_of_isOpen m hA hx).symm

/-! ## The circle points lie in the closure of the two halves -/

/-- A point on the sphere `‖z‖ = ρ` above `x ∈ U` lies in the closure of the inner region
`U × {a < ‖z‖ < ρ}` (when `a < ρ` and `ρ > 0`). -/
lemma mem_closure_reg_inner {U : Set X} {a ρ : ℝ} (haρ : a < ρ) (hρpos : 0 < ρ) {x : X}
    (hx : x ∈ U) {z : ℂ} (hz : ‖z‖ = ρ) : (x, z) ∈ closure (reg U a ρ) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min (ε / 2) (min ((ρ - a) / 2) (ρ / 2)) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδa : δ ≤ (ρ - a) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδρ : δ < ρ := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  set t : ℝ := (ρ - δ) / ρ with htdef
  have ht0 : 0 < t := div_pos (by linarith) hρpos
  have ht1 : t < 1 := by rw [htdef, div_lt_one hρpos]; linarith
  have hnorm : ‖(t : ℂ) * z‖ = ρ - δ := by
    rw [norm_mul, norm_coe_real, abs_of_pos ht0, hz, htdef,
      div_mul_cancel₀ _ (ne_of_gt hρpos)]
  refine ⟨(x, (t : ℂ) * z), ?_, ?_⟩
  · rw [mem_reg_iff]
    refine ⟨hx, ?_, ?_⟩
    · show a < ‖(t : ℂ) * z‖
      rw [hnorm]; linarith
    · show ‖(t : ℂ) * z‖ < ρ
      rw [hnorm]; linarith
  · rw [dist_eq_norm]
    have hpair : (x, z) - (x, (t : ℂ) * z) = (0, z - (t : ℂ) * z) := by simp
    rw [hpair, show ‖((0 : X), z - (t : ℂ) * z)‖ = ‖z - (t : ℂ) * z‖ from by
      simp [Prod.norm_def]]
    have heq : z - (t : ℂ) * z = ((1 - t : ℝ) : ℂ) * z := by push_cast; ring
    rw [heq, norm_mul, norm_coe_real, abs_of_pos (by linarith [ht1]), hz]
    have hstep : (1 - t) * ρ = δ := by rw [htdef]; field_simp; ring
    rw [hstep]
    exact hδε

/-- A point on the sphere `‖z‖ = ρ` above `x ∈ U` lies in the closure of the outer region
`U × {ρ < ‖z‖ < d}` (when `ρ < d`). -/
lemma mem_closure_reg_outer {U : Set X} {ρ d : ℝ} (hρd : ρ < d) {x : X} (hx : x ∈ U) {z : ℂ}
    (hz : ‖z‖ = ρ) : (x, z) ∈ closure (reg U ρ d) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min (ε / 2) ((d - ρ) / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδd : δ ≤ (d - ρ) / 2 := min_le_right _ _
  set z' : ℂ := if z = 0 then (δ : ℂ) else ((1 + δ / ρ : ℝ) : ℂ) * z with hz'def
  have hnorm : ‖z'‖ = ρ + δ := by
    by_cases hz0 : z = 0
    · have hρ0 : ρ = 0 := by rw [← hz]; simp [hz0]
      rw [hz'def, if_pos hz0, norm_coe_real, abs_of_pos hδpos, hρ0, zero_add]
    · have hρpos : 0 < ρ := by rw [← hz]; exact norm_pos_iff.mpr hz0
      have h1p : 0 < 1 + δ / ρ := by positivity
      rw [hz'def, if_neg hz0, norm_mul, norm_coe_real]
      rw [abs_of_pos h1p, hz]
      field_simp
  have hdist : ‖z' - z‖ = δ := by
    by_cases hz0 : z = 0
    · subst hz0
      rw [hz'def, if_pos rfl, sub_zero, norm_coe_real, abs_of_pos hδpos]
    · have hρpos : 0 < ρ := by rw [← hz]; exact norm_pos_iff.mpr hz0
      rw [hz'def, if_neg hz0]
      have heq : ((1 + δ / ρ : ℝ) : ℂ) * z - z = ((δ / ρ : ℝ) : ℂ) * z := by
        push_cast; ring
      rw [heq, norm_mul, norm_coe_real]
      rw [abs_of_pos (div_pos hδpos hρpos), hz]
      field_simp
  refine ⟨(x, z'), ?_, ?_⟩
  · rw [mem_reg_iff]
    refine ⟨hx, ?_, ?_⟩
    · show ρ < ‖z'‖
      rw [hnorm]; linarith
    · show ‖z'‖ < d
      rw [hnorm]; linarith
  · rw [dist_eq_norm]
    have hpair : (x, z) - (x, z') = (0, z - z') := by simp
    rw [hpair, show ‖((0 : X), z - z')‖ = ‖z - z'‖ from by simp [Prod.norm_def]]
    rw [norm_sub_rev z z', hdist]
    exact hδε

lemma reg_subset_closure_split {U : Set X} {a ρ d : ℝ} (haρ : a < ρ) (hρd : ρ < d) :
    reg U a d ⊆ closure (reg U a ρ ∪ reg U ρ d) := by
  intro p hp
  rw [mem_reg_iff] at hp
  obtain ⟨hx, haz, hzd⟩ := hp
  rcases lt_trichotomy ‖p.2‖ ρ with h | h | h
  · exact subset_closure (Or.inl (by rw [mem_reg_iff]; exact ⟨hx, haz, h⟩))
  · exact closure_mono subset_union_right (mem_closure_reg_outer hρd hx h)
  · exact subset_closure (Or.inr (by rw [mem_reg_iff]; exact ⟨hx, h, hzd⟩))

/-! ## A circle point on the segment between an inner and an outer point -/

lemma exists_norm_eq_rho_segment {z₁ z₂ : ℂ} {ρ : ℝ} (h1 : ‖z₁‖ < ρ) (h2 : ρ < ‖z₂‖) :
    ∃ c : ℂ, ‖c‖ = ρ ∧ ‖z₁ - c‖ ≤ ‖z₁ - z₂‖ ∧ ‖z₂ - c‖ ≤ ‖z₁ - z₂‖ := by
  have hcont : Continuous (fun t : ℝ => ‖(1 - t) • z₁ + t • z₂‖) :=
    (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)).norm
  have hmem : ρ ∈ Icc (‖(1 - (0:ℝ)) • z₁ + (0:ℝ) • z₂‖)
      (‖(1 - (1:ℝ)) • z₁ + (1:ℝ) • z₂‖) := by
    constructor
    · simpa using le_of_lt h1
    · simpa using le_of_lt h2
  obtain ⟨t, ht, htval⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
    hcont.continuousOn hmem
  refine ⟨(1 - t) • z₁ + t • z₂, htval, ?_, ?_⟩
  · have heq : z₁ - ((1 - t) • z₁ + t • z₂) = t • (z₁ - z₂) := by
      simp only [Complex.real_smul]; push_cast; ring
    rw [heq, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖z₁ - z₂‖ ≤ 1 * ‖z₁ - z₂‖ :=
          mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) (norm_nonneg _)
      _ = ‖z₁ - z₂‖ := one_mul _
  · have heq : z₂ - ((1 - t) • z₁ + t • z₂) = (1 - t) • (z₂ - z₁) := by
      simp only [Complex.real_smul]; push_cast; ring
    rw [heq, norm_smul, Real.norm_eq_abs]
    calc |1 - t| * ‖z₂ - z₁‖ ≤ 1 * ‖z₂ - z₁‖ :=
          mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩)
            (norm_nonneg _)
      _ = ‖z₂ - z₁‖ := one_mul _
      _ = ‖z₁ - z₂‖ := (norm_sub_rev z₁ z₂).symm

/-! ## Bridging the `Within` and ambient iterated derivatives -/

lemma iterDerivNorm_eq_iSup {m : ℕ} {f : X × ℂ → ℂ} {A : Set (X × ℂ)} (hA : IsOpen A) :
    iterDerivNorm m f A = ⨆ y ∈ A, ENNReal.ofReal ‖iteratedFDeriv ℝ m f y‖ := by
  rw [iterDerivNorm]
  exact iSup_congr fun y => iSup_congr fun hy => by
    rw [iteratedFDerivWithin_of_isOpen m hA hy]

/-! ## Extension of the Hölder bound to the closure of a half -/

/-- If `D` is open and `D ⊆ A` with `f` of class `C^k` on the open set `A`, then for
`p ∈ D` and `r ∈ A ∩ closure D`, `r ≠ p`, the Hölder seminorm of `D` controls the
difference of the `m`-th derivatives between `p` and `r` (`m ≤ k`). -/
lemma holderSeminorm_pair_le_of_mem_closure {m k : ℕ} {α : ℝ} (hα : 0 < α)
    {A D : Set (X × ℂ)} (hA : IsOpen A) (hD : IsOpen D)
    {f : X × ℂ → ℂ} (hf : ContDiffOn ℝ (k : WithTop ENat) f A) (hmk : m ≤ k)
    {p r : X × ℂ} (hp : p ∈ D) (hrA : r ∈ A) (hr : r ∈ closure D) (hrp : r ≠ p) :
    ENNReal.ofReal (‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f r‖ / ‖p - r‖ ^ α)
      ≤ holderSeminorm m α f D := by
  have hgcont : ContinuousAt (iteratedFDeriv ℝ m f) r :=
    (continuousOn_iteratedFDeriv_of_contDiffOn hA hf hmk).continuousAt (hA.mem_nhds hrA)
  haveI : (𝓝[D] r).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hr
  set h : X × ℂ → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f y‖ / ‖p - y‖ ^ α)
    with hh
  have hcont : ContinuousAt h r := by
    refine ENNReal.continuous_ofReal.continuousAt.comp ?_
    have h1 : ContinuousAt (fun y : X × ℂ => ‖iteratedFDeriv ℝ m f p -
        iteratedFDeriv ℝ m f y‖) r := (continuousAt_const.sub hgcont).norm
    have h2 : ContinuousAt (fun y : X × ℂ => ‖p - y‖ ^ α) r :=
      (continuousAt_const.sub continuousAt_id).norm.rpow_const (Or.inr (le_of_lt hα))
    refine h1.div h2 ?_
    exact ne_of_gt (Real.rpow_pos_of_pos (by rw [norm_pos_iff]; exact sub_ne_zero.mpr (Ne.symm hrp)) α)
  have hev : ∀ᶠ y in 𝓝[D] r, h y ≤ holderSeminorm m α f D := by
    have hne : ∀ᶠ y in 𝓝[D] r, y ≠ p :=
      (eventually_ne_nhds hrp).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hne] with y hyD hyp
    simp only [hh]
    have hmem := le_holderSeminorm m α f D hp hyD (Ne.symm hyp)
    rwa [iteratedFDerivWithin_of_isOpen m hD hp,
      iteratedFDerivWithin_of_isOpen m hD hyD] at hmem
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev

/-! ## The crossing bound -/

/-- For `p` in the inner half and `q` in the outer half, the Hölder difference quotient of
the `m`-th derivatives across the circle `‖z‖ = ρ` is controlled by the sum of the two
halves' seminorms. -/
lemma cross_bound {m k : ℕ} {α : ℝ} (hα : 0 < α) {U : Set X} {a ρ d : ℝ}
    (hU : IsOpen U) (haρ : a < ρ) (hρd : ρ < d) {f : X × ℂ → ℂ}
    (hf : ContDiffOn ℝ (k : WithTop ENat) f (reg U a d)) (hmk : m ≤ k)
    {s1 s2 : ℝ} (hs1nn : 0 ≤ s1) (hs2nn : 0 ≤ s2)
    (hb1 : holderSeminorm m α f (reg U a ρ) = ENNReal.ofReal s1)
    (hb2 : holderSeminorm m α f (reg U ρ d) = ENNReal.ofReal s2)
    {p q : X × ℂ} (hp : p ∈ reg U a ρ) (hq : q ∈ reg U ρ d) (hpq : p ≠ q) :
    ENNReal.ofReal (‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f q‖ / ‖p - q‖ ^ α)
      ≤ 2 * (ENNReal.ofReal s1 + ENNReal.ofReal s2) := by
  have hA : IsOpen (reg U a d) := isOpen_reg hU a d
  have hA1 : IsOpen (reg U a ρ) := isOpen_reg hU a ρ
  have hA2 : IsOpen (reg U ρ d) := isOpen_reg hU ρ d
  rw [mem_reg_iff] at hp hq
  obtain ⟨c, hc, hc1, hc2⟩ := exists_norm_eq_rho_segment hp.2.2 hq.2.1
  have hρpos : 0 < ρ := lt_of_le_of_lt (norm_nonneg p.2) hp.2.2
  have hrrcA : (p.1, c) ∈ reg U a d := by
    rw [mem_reg_iff]
    exact ⟨hp.1, by rw [hc]; exact haρ, by rw [hc]; exact hρd⟩
  have hrrc1 : (p.1, c) ∈ closure (reg U a ρ) := mem_closure_reg_inner haρ hρpos hp.1 hc
  have hrrc2 : (p.1, c) ∈ closure (reg U ρ d) := mem_closure_reg_outer hρd hp.1 hc
  have hne1 : (p.1, c) ≠ p := by
    intro hEq
    have h2 : c = p.2 := by simpa using congrArg Prod.snd hEq
    rw [h2] at hc; linarith [hp.2.2]
  have hne2 : (p.1, c) ≠ q := by
    intro hEq
    have h2 : c = q.2 := by simpa using congrArg Prod.snd hEq
    rw [h2] at hc; linarith [hq.2.1]
  have he1 := holderSeminorm_pair_le_of_mem_closure hα hA hA1 hf hmk hp hrrcA hrrc1 hne1
  have he2 := holderSeminorm_pair_le_of_mem_closure hα hA hA2 hf hmk hq hrrcA hrrc2 hne2
  rw [hb1] at he1
  rw [hb2] at he2
  have hb1' : ‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f (p.1, c)‖
      ≤ s1 * ‖p - (p.1, c)‖ ^ α := by
    have hgd := (ENNReal.ofReal_le_ofReal_iff hs1nn).mp he1
    have hd : 0 < ‖p - (p.1, c)‖ ^ α :=
      Real.rpow_pos_of_pos (by rw [norm_pos_iff]; exact sub_ne_zero.mpr (Ne.symm hne1)) α
    calc ‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f (p.1, c)‖
        = (‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f (p.1, c)‖ /
            ‖p - (p.1, c)‖ ^ α) * ‖p - (p.1, c)‖ ^ α :=
          (div_mul_cancel₀ _ (ne_of_gt hd)).symm
      _ ≤ s1 * ‖p - (p.1, c)‖ ^ α := mul_le_mul_of_nonneg_right hgd (le_of_lt hd)
  have hb2' : ‖iteratedFDeriv ℝ m f q - iteratedFDeriv ℝ m f (p.1, c)‖
      ≤ s2 * ‖q - (p.1, c)‖ ^ α := by
    have hgd := (ENNReal.ofReal_le_ofReal_iff hs2nn).mp he2
    have hd : 0 < ‖q - (p.1, c)‖ ^ α :=
      Real.rpow_pos_of_pos (by rw [norm_pos_iff]; exact sub_ne_zero.mpr (Ne.symm hne2)) α
    calc ‖iteratedFDeriv ℝ m f q - iteratedFDeriv ℝ m f (p.1, c)‖
        = (‖iteratedFDeriv ℝ m f q - iteratedFDeriv ℝ m f (p.1, c)‖ /
            ‖q - (p.1, c)‖ ^ α) * ‖q - (p.1, c)‖ ^ α :=
          (div_mul_cancel₀ _ (ne_of_gt hd)).symm
      _ ≤ s2 * ‖q - (p.1, c)‖ ^ α := mul_le_mul_of_nonneg_right hgd (le_of_lt hd)
  have hd1R : ‖p - (p.1, c)‖ ≤ ‖p - q‖ := by
    rw [Prod.norm_def, Prod.norm_def]
    rw [show (p - (p.1, c)).1 = 0 from by simp, show (p - (p.1, c)).2 = p.2 - c from by simp,
        show (p - q).1 = p.1 - q.1 from by simp, show (p - q).2 = p.2 - q.2 from by simp]
    refine max_le (by simp) ?_
    calc ‖p.2 - c‖ ≤ ‖p.2 - q.2‖ := hc1
      _ ≤ max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := le_max_right _ _
  have hd2R : ‖q - (p.1, c)‖ ≤ ‖p - q‖ := by
    rw [Prod.norm_def, Prod.norm_def]
    rw [show (q - (p.1, c)).1 = q.1 - p.1 from by simp, show (q - (p.1, c)).2 = q.2 - c from by simp,
        show (p - q).1 = p.1 - q.1 from by simp, show (p - q).2 = p.2 - q.2 from by simp]
    refine max_le ?_ ?_
    · rw [norm_sub_rev]; exact le_max_left _ _
    · calc ‖q.2 - c‖ ≤ ‖p.2 - q.2‖ := hc2
        _ ≤ max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := le_max_right _ _
  have hRpos : 0 < ‖p - q‖ ^ α :=
    Real.rpow_pos_of_pos (by rw [norm_pos_iff]; exact sub_ne_zero.mpr hpq) α
  have hkey : ‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f q‖
      ≤ (s1 + s2) * ‖p - q‖ ^ α := by
    have h1 : ‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f q‖
        ≤ ‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f (p.1, c)‖
          + ‖iteratedFDeriv ℝ m f q - iteratedFDeriv ℝ m f (p.1, c)‖ := by
      calc ‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f q‖
          = ‖(iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f (p.1, c))
              - (iteratedFDeriv ℝ m f q - iteratedFDeriv ℝ m f (p.1, c))‖ := by
            simp only [sub_sub_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    have h2 : s1 * ‖p - (p.1, c)‖ ^ α + s2 * ‖q - (p.1, c)‖ ^ α
        ≤ (s1 + s2) * ‖p - q‖ ^ α := by
      have e1 : ‖p - (p.1, c)‖ ^ α ≤ ‖p - q‖ ^ α :=
        Real.rpow_le_rpow (norm_nonneg _) hd1R (le_of_lt hα)
      have e2 : ‖q - (p.1, c)‖ ^ α ≤ ‖p - q‖ ^ α :=
        Real.rpow_le_rpow (norm_nonneg _) hd2R (le_of_lt hα)
      nlinarith [mul_le_mul_of_nonneg_left e1 hs1nn, mul_le_mul_of_nonneg_left e2 hs2nn]
    linarith [h1, hb1', hb2', h2]
  have hgoal : ‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f q‖ / ‖p - q‖ ^ α ≤ s1 + s2 := by
    rw [div_le_iff₀ hRpos]
    linarith [hkey]
  calc ENNReal.ofReal (‖iteratedFDeriv ℝ m f p - iteratedFDeriv ℝ m f q‖ / ‖p - q‖ ^ α)
      ≤ ENNReal.ofReal (s1 + s2) := ENNReal.ofReal_le_ofReal hgoal
    _ = ENNReal.ofReal s1 + ENNReal.ofReal s2 := ENNReal.ofReal_add hs1nn hs2nn
    _ ≤ 2 * (ENNReal.ofReal s1 + ENNReal.ofReal s2) := by
        rw [two_mul]; exact le_self_add

/-! ## The two per-level estimates -/

lemma iterDerivNorm_le_split {k m : ℕ} {U : Set X} {a ρ d : ℝ} (hU : IsOpen U)
    (haρ : a < ρ) (hρd : ρ < d) {f : X × ℂ → ℂ}
    (hf : ContDiffOn ℝ (k : WithTop ENat) f (reg U a d)) (hmk : m ≤ k) :
    iterDerivNorm m f (reg U a d) ≤ iterDerivNorm m f (reg U a ρ) + iterDerivNorm m f (reg U ρ d) := by
  have hA : IsOpen (reg U a d) := isOpen_reg hU a d
  have hA1 : IsOpen (reg U a ρ) := isOpen_reg hU a ρ
  have hA2 : IsOpen (reg U ρ d) := isOpen_reg hU ρ d
  have hcont : ContinuousOn (fun y : X × ℂ => ENNReal.ofReal ‖iteratedFDeriv ℝ m f y‖)
      (reg U a d) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_iteratedFDeriv_of_contDiffOn hA hf hmk).norm)
  have hsub : reg U a ρ ∪ reg U ρ d ⊆ reg U a d := by
    intro p hp
    rcases hp with hp | hp <;> rw [mem_reg_iff] at hp ⊢
    · exact ⟨hp.1, hp.2.1, lt_trans hp.2.2 hρd⟩
    · exact ⟨hp.1, lt_trans haρ hp.2.1, hp.2.2⟩
  calc iterDerivNorm m f (reg U a d)
      = ⨆ y ∈ reg U a d, ENNReal.ofReal ‖iteratedFDeriv ℝ m f y‖ := iterDerivNorm_eq_iSup hA
    _ ≤ ⨆ y ∈ reg U a ρ ∪ reg U ρ d, ENNReal.ofReal ‖iteratedFDeriv ℝ m f y‖ :=
        iSup_le_iSup_of_subset_closure hcont hsub (reg_subset_closure_split haρ hρd)
    _ = (⨆ y ∈ reg U a ρ, ENNReal.ofReal ‖iteratedFDeriv ℝ m f y‖)
          ⊔ (⨆ y ∈ reg U ρ d, ENNReal.ofReal ‖iteratedFDeriv ℝ m f y‖) := iSup_union
    _ ≤ iterDerivNorm m f (reg U a ρ) + iterDerivNorm m f (reg U ρ d) := by
        rw [iterDerivNorm_eq_iSup hA1, iterDerivNorm_eq_iSup hA2]
        exact sup_le le_self_add le_add_self

lemma holderSeminorm_le_split {k m : ℕ} {α : ℝ} (hα : 0 < α) {U : Set X} {a ρ d : ℝ}
    (hU : IsOpen U) (haρ : a < ρ) (hρd : ρ < d) {f : X × ℂ → ℂ}
    (hf : ContDiffOn ℝ (k : WithTop ENat) f (reg U a d)) (hmk : m ≤ k) :
    holderSeminorm m α f (reg U a d)
      ≤ 2 * (holderSeminorm m α f (reg U a ρ) + holderSeminorm m α f (reg U ρ d)) := by
  have hA : IsOpen (reg U a d) := isOpen_reg hU a d
  have hA1 : IsOpen (reg U a ρ) := isOpen_reg hU a ρ
  have hA2 : IsOpen (reg U ρ d) := isOpen_reg hU ρ d
  by_cases htop : holderSeminorm m α f (reg U a ρ) = ⊤ ∨ holderSeminorm m α f (reg U ρ d) = ⊤
  · rcases htop with h | h <;> rw [h] <;> simp
  · obtain ⟨h1ne, h2ne⟩ : holderSeminorm m α f (reg U a ρ) ≠ ⊤ ∧
        holderSeminorm m α f (reg U ρ d) ≠ ⊤ := by
      simpa [not_or] using htop
    set s1 : ℝ := (holderSeminorm m α f (reg U a ρ)).toReal with hs1def
    set s2 : ℝ := (holderSeminorm m α f (reg U ρ d)).toReal with hs2def
    have hs1 : holderSeminorm m α f (reg U a ρ) = ENNReal.ofReal s1 :=
      (ENNReal.ofReal_toReal h1ne).symm
    have hs2 : holderSeminorm m α f (reg U ρ d) = ENNReal.ofReal s2 :=
      (ENNReal.ofReal_toReal h2ne).symm
    have hs1nn : 0 ≤ s1 := ENNReal.toReal_nonneg
    have hs2nn : 0 ≤ s2 := ENNReal.toReal_nonneg
    rw [hs1, hs2]
    set D : Set (X × ℂ) := reg U a ρ ∪ reg U ρ d with hDdef
    set G : (X × ℂ) × (X × ℂ) → ℝ≥0∞ :=
      fun r => ENNReal.ofReal
        (‖iteratedFDeriv ℝ m f r.1 - iteratedFDeriv ℝ m f r.2‖ / ‖r.1 - r.2‖ ^ α) with hGdef
    set OApair : Set ((X × ℂ) × (X × ℂ)) :=
      {r | r.1 ∈ reg U a d ∧ r.2 ∈ reg U a d ∧ r.1 ≠ r.2} with hOApairdef
    set ODpair : Set ((X × ℂ) × (X × ℂ)) :=
      {r | r.1 ∈ D ∧ r.2 ∈ D ∧ r.1 ≠ r.2} with hODpairdef
    have hstep1 : holderSeminorm m α f (reg U a d) ≤ ⨆ r ∈ OApair, G r := by
      rw [holderSeminorm]
      refine iSup_le fun p => iSup_le fun hp => iSup_le fun q => iSup_le fun hq =>
        iSup_le fun hpq => ?_
      simp only [hOApairdef, hGdef]
      rw [iteratedFDerivWithin_of_isOpen m hA hp, iteratedFDerivWithin_of_isOpen m hA hq]
      exact le_iSup₂_of_le (p, q) ⟨hp, hq, hpq⟩ le_rfl
    have hODsubOA : ODpair ⊆ OApair := by
      intro r hr
      obtain ⟨hr1, hr2, hrne⟩ := hr
      refine ⟨?_, ?_, hrne⟩
      · rcases hr1 with hr1 | hr1 <;> rw [mem_reg_iff] at hr1 ⊢
        · exact ⟨hr1.1, hr1.2.1, lt_trans hr1.2.2 hρd⟩
        · exact ⟨hr1.1, lt_trans haρ hr1.2.1, hr1.2.2⟩
      · rcases hr2 with hr2 | hr2 <;> rw [mem_reg_iff] at hr2 ⊢
        · exact ⟨hr2.1, hr2.2.1, lt_trans hr2.2.2 hρd⟩
        · exact ⟨hr2.1, lt_trans haρ hr2.2.1, hr2.2.2⟩
    have hOAcl : OApair ⊆ closure ODpair := by
      intro r hr
      obtain ⟨hr1, hr2, hrne⟩ := hr
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hd1 : ∀ η > 0, ∃ b ∈ D, dist r.1 b < η := by
        rw [← Metric.mem_closure_iff, hDdef]
        exact reg_subset_closure_split haρ hρd hr1
      have hd2 : ∀ η > 0, ∃ b ∈ D, dist r.2 b < η := by
        rw [← Metric.mem_closure_iff, hDdef]
        exact reg_subset_closure_split haρ hρd hr2
      have hdist : 0 < dist r.1 r.2 := dist_pos.mpr hrne
      set η : ℝ := min (ε / 3) (dist r.1 r.2 / 3) with hηdef
      have hηpos : 0 < η := lt_min (by linarith) (by linarith)
      have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hηd : η ≤ dist r.1 r.2 / 3 := min_le_right _ _
      obtain ⟨d1, hd1m, hd1lt⟩ := hd1 η hηpos
      obtain ⟨d2, hd2m, hd2lt⟩ := hd2 η hηpos
      have hne : d1 ≠ d2 := by
        intro hEq
        have hle : dist r.1 r.2 ≤ dist r.1 d1 + dist d2 r.2 := by
          rw [← hEq]; exact dist_triangle _ _ _
        rw [dist_comm d2 r.2] at hle
        have h2 : dist r.1 d1 + dist r.2 d2 < 2 * η := by linarith
        have h3 : 2 * η ≤ 2 * (dist r.1 r.2 / 3) := by linarith
        linarith
      exact ⟨(d1, d2), ⟨hd1m, hd2m, hne⟩, by
        rw [Prod.dist_eq]
        exact lt_of_lt_of_le (max_lt hd1lt hd2lt) (le_of_lt hηε)⟩
    have hGcont : ContinuousOn G OApair := by
      have hgfst : ContinuousOn (fun r : (X × ℂ) × (X × ℂ) => iteratedFDeriv ℝ m f r.1) OApair :=
        (continuousOn_iteratedFDeriv_of_contDiffOn hA hf hmk).comp continuous_fst.continuousOn
          (fun r hr => hr.1)
      have hgsnd : ContinuousOn (fun r : (X × ℂ) × (X × ℂ) => iteratedFDeriv ℝ m f r.2) OApair :=
        (continuousOn_iteratedFDeriv_of_contDiffOn hA hf hmk).comp continuous_snd.continuousOn
          (fun r hr => hr.2.1)
      have hnum : ContinuousOn (fun r : (X × ℂ) × (X × ℂ) =>
          ‖iteratedFDeriv ℝ m f r.1 - iteratedFDeriv ℝ m f r.2‖) OApair :=
        (hgfst.sub hgsnd).norm
      have hbase : ContinuousOn (fun r : (X × ℂ) × (X × ℂ) => ‖r.1 - r.2‖) OApair :=
        ((continuous_fst.sub continuous_snd).continuousOn).norm
      have hden : ContinuousOn (fun r : (X × ℂ) × (X × ℂ) => ‖r.1 - r.2‖ ^ α) OApair :=
        hbase.rpow continuousOn_const (fun r hr => Or.inr hα)
      have hdiv : ContinuousOn (fun r : (X × ℂ) × (X × ℂ) =>
          ‖iteratedFDeriv ℝ m f r.1 - iteratedFDeriv ℝ m f r.2‖ / ‖r.1 - r.2‖ ^ α) OApair :=
        hnum.div hden (fun r hr => ne_of_gt (Real.rpow_pos_of_pos
          (by rw [norm_pos_iff]; exact sub_ne_zero.mpr hr.2.2) α))
      exact ENNReal.continuous_ofReal.comp_continuousOn hdiv
    have hstep2 : (⨆ r ∈ OApair, G r) ≤ ⨆ r ∈ ODpair, G r :=
      iSup_le_iSup_of_subset_closure hGcont hODsubOA hOAcl
    have hstep3 : (⨆ r ∈ ODpair, G r) ≤ 2 * (ENNReal.ofReal s1 + ENNReal.ofReal s2) := by
      refine iSup_le fun r => iSup_le fun hr => ?_
      obtain ⟨hr1, hr2, hrne⟩ := hr
      rcases hr1 with hr1 | hr1 <;> rcases hr2 with hr2 | hr2
      · -- both in the inner half
        have hb : ENNReal.ofReal (‖iteratedFDeriv ℝ m f r.1 - iteratedFDeriv ℝ m f r.2‖ /
            ‖r.1 - r.2‖ ^ α) ≤ holderSeminorm m α f (reg U a ρ) := by
          have hmem := le_holderSeminorm m α f (reg U a ρ) hr1 hr2 hrne
          rwa [iteratedFDerivWithin_of_isOpen m hA1 hr1,
            iteratedFDerivWithin_of_isOpen m hA1 hr2] at hmem
        calc G r ≤ holderSeminorm m α f (reg U a ρ) := hb
          _ = ENNReal.ofReal s1 := hs1
          _ ≤ 2 * (ENNReal.ofReal s1 + ENNReal.ofReal s2) := by
              rw [two_mul]; exact le_trans le_self_add le_add_self
      · -- `r.1` inner, `r.2` outer : the crossing case
        exact cross_bound hα hU haρ hρd hf hmk hs1nn hs2nn hs1 hs2 hr1 hr2 hrne
      · -- `r.1` outer, `r.2` inner : the crossing case, with the roles swapped
        have h := cross_bound hα hU haρ hρd hf hmk hs1nn hs2nn hs1 hs2 hr2 hr1 (Ne.symm hrne)
        have heq : G r = ENNReal.ofReal (‖iteratedFDeriv ℝ m f r.2 - iteratedFDeriv ℝ m f r.1‖
            / ‖r.2 - r.1‖ ^ α) := by
          rw [hGdef]
          simp only [norm_sub_rev]
        rw [heq]; exact h
      · -- both in the outer half
        have hb : ENNReal.ofReal (‖iteratedFDeriv ℝ m f r.1 - iteratedFDeriv ℝ m f r.2‖ /
            ‖r.1 - r.2‖ ^ α) ≤ holderSeminorm m α f (reg U ρ d) := by
          have hmem := le_holderSeminorm m α f (reg U ρ d) hr1 hr2 hrne
          rwa [iteratedFDerivWithin_of_isOpen m hA2 hr1,
            iteratedFDerivWithin_of_isOpen m hA2 hr2] at hmem
        calc G r ≤ holderSeminorm m α f (reg U ρ d) := hb
          _ = ENNReal.ofReal s2 := hs2
          _ ≤ 2 * (ENNReal.ofReal s1 + ENNReal.ofReal s2) := by
              rw [two_mul]; exact le_trans le_add_self le_add_self
    calc holderSeminorm m α f (reg U a d) ≤ ⨆ r ∈ OApair, G r := hstep1
      _ ≤ ⨆ r ∈ ODpair, G r := hstep2
      _ ≤ 2 * (ENNReal.ofReal s1 + ENNReal.ofReal s2) := hstep3

/-! ## The main estimate -/

lemma holderNorm_le_split {k : ℕ} {α : ℝ} (hα : 0 < α) {U : Set X} {a ρ d : ℝ}
    (hU : IsOpen U) (haρ : a < ρ) (hρd : ρ < d) {f : X × ℂ → ℂ}
    (hf : ContDiffOn ℝ (k : WithTop ENat) f (reg U a d)) :
    holderNorm k α f (reg U a d)
      ≤ 2 * (holderNorm k α f (reg U a ρ) + holderNorm k α f (reg U ρ d)) := by
  have hterm : ∀ i ∈ Finset.range (k + 1),
      iterDerivNorm i f (reg U a d) + holderSeminorm i α f (reg U a d)
        ≤ 2 * ((iterDerivNorm i f (reg U a ρ) + holderSeminorm i α f (reg U a ρ))
              + (iterDerivNorm i f (reg U ρ d) + holderSeminorm i α f (reg U ρ d))) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hid := iterDerivNorm_le_split hU haρ hρd hf hik
    have hhs := holderSeminorm_le_split hα hU haρ hρd hf hik
    have h1 : iterDerivNorm i f (reg U a d) + holderSeminorm i α f (reg U a d)
        ≤ (iterDerivNorm i f (reg U a ρ) + iterDerivNorm i f (reg U ρ d))
          + 2 * (holderSeminorm i α f (reg U a ρ) + holderSeminorm i α f (reg U ρ d)) :=
      add_le_add hid hhs
    have h2 : (iterDerivNorm i f (reg U a ρ) + iterDerivNorm i f (reg U ρ d))
          + 2 * (holderSeminorm i α f (reg U a ρ) + holderSeminorm i α f (reg U ρ d))
        ≤ 2 * ((iterDerivNorm i f (reg U a ρ) + holderSeminorm i α f (reg U a ρ))
              + (iterDerivNorm i f (reg U ρ d) + holderSeminorm i α f (reg U ρ d))) := by
      rw [show 2 * ((iterDerivNorm i f (reg U a ρ) + holderSeminorm i α f (reg U a ρ))
              + (iterDerivNorm i f (reg U ρ d) + holderSeminorm i α f (reg U ρ d)))
            = ((iterDerivNorm i f (reg U a ρ) + iterDerivNorm i f (reg U ρ d))
                + 2 * (holderSeminorm i α f (reg U a ρ) + holderSeminorm i α f (reg U ρ d)))
              + (iterDerivNorm i f (reg U a ρ) + iterDerivNorm i f (reg U ρ d)) from by ring]
      exact le_self_add
    exact le_trans h1 h2
  calc holderNorm k α f (reg U a d)
      = ∑ i ∈ Finset.range (k + 1),
          (iterDerivNorm i f (reg U a d) + holderSeminorm i α f (reg U a d)) := rfl
    _ ≤ ∑ i ∈ Finset.range (k + 1),
          2 * ((iterDerivNorm i f (reg U a ρ) + holderSeminorm i α f (reg U a ρ))
              + (iterDerivNorm i f (reg U ρ d) + holderSeminorm i α f (reg U ρ d))) :=
        Finset.sum_le_sum hterm
    _ = 2 * (holderNorm k α f (reg U a ρ) + holderNorm k α f (reg U ρ d)) := by
        simp only [holderNorm]
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_add, mul_add, mul_add]

theorem holderNorm_radial_split {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {α : ℝ}
    (hα : 0 < α) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧
      ∀ (k : ℕ) (U : Set X) (a ρ d : ℝ), IsOpen U → a < ρ → ρ < d →
      ∀ f : X × ℂ → ℂ, ContDiffOn ℝ (k : WithTop ENat) f (U ×ˢ {z : ℂ | a < ‖z‖ ∧ ‖z‖ < d}) →
      Work.CR.Flat.holderNorm k α f (U ×ˢ {z : ℂ | a < ‖z‖ ∧ ‖z‖ < d})
        ≤ ENNReal.ofReal (K k) * (Work.CR.Flat.holderNorm k α f (U ×ˢ {z : ℂ | a < ‖z‖ ∧ ‖z‖ < ρ})
            + Work.CR.Flat.holderNorm k α f (U ×ˢ {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < d})) := by
  refine ⟨fun _ => 2, fun k => by norm_num, ?_⟩
  intro k U a ρ d hU haρ hρd f hf
  have hK : ENNReal.ofReal ((fun _ : ℕ => (2 : ℝ)) k) = 2 := by
    norm_num [ENNReal.ofReal_ofNat]
  rw [hK]
  simpa only [reg, ann] using holderNorm_le_split hα hU haρ hρd hf

end Work.NN.DiscRadial
