import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.collarChart_flat
import Submission.Work.RPB.B5.chartLev_contDiffOn
import Submission.Work.RPB.B5.lagPt_negSqrt2_decomp
import Submission.Work.RPB.B5.collarPt_contDiffWithinAt
import Submission.Work.RPB.B5.slabExtendPeriodic
import Submission.Work.RPB.B5.contDiff_piecewise_param

/-!
# B5: smoothness of the assembled family at the junction `x = √2`

The assembled family `ℓ = lagPt W Γc Ac rho` is

* `basePt … τ x t` for `x ≤ 0` (the collar for `x ≤ -√2`, the chord chart for `-√2 ≤ x ≤ 0`),
* `tau π (basePt … τ (-x) (t - π))` for `x > 0`.

Hence the point `x = +√2` is the `tau π`-transport of the *collar/chart junction* `x = -√2`:
writing `σ = sig x = x²/2 - 1`, the two branches of `basePt` near `x = -√2` are the collar
`collarPt Γc Ac τ σ t` and the chord profile `W τ t (ρh τ t σ)` (the second because
`rho τ x t = ρh τ t (sig x)` on a two-sided window of `-√2`, hypothesis `hrhonearδ`), and they
agree at `σ = 0` together with all one-sided `σ`-jets up to order `8` (hypothesis `σjet`,
equivalently `collarChart_flat`).

The proof writes `basePt`, near `x = -√2`, as
`(τ,x,t) ↦ chartP (τ, t, sig x) + truncP (τ, t, sig x)` with
`chartP (τ,t,σ) = W τ t (ρh τ t σ)` and `truncP = the flat truncation of collar − chart`, and
obtains smoothness of the two summands separately:

* `chartP` from `chartLev_contDiffOn` (the level inverse `ρh` maps into the box of `W`);
* `truncP` from the flat-truncation lemma `flatTrunc_slab_point_local`, whose flatness hypothesis
  is exactly `collarChart_flat`.  That lemma is proved below: the `τ ∈ [0,1]`-restriction of the
  data is removed by extending `h` across the seams `τ = 0` and `τ = 1` (the latter after the
  substitution `τ ↦ 1 - τ`) by the finite Seeley reflection, and then truncating in `σ` with
  `contDiff_piecewise_param`.

Finally the reflection `x ↦ -x` (with `t ↦ t - π`), the map `τ_π` and the congruence along
`lagPt_negSqrt2_decomp` complete the argument.
-/

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Two bookkeeping lemmas about one-sided derivatives -/

/-- `Ici 0 = insert 0 (Ioi 0)`. -/
private lemma Ici_zero_eq_insert_Ioi_sqrt2 : Set.Ici (0 : ℝ) = insert 0 (Set.Ioi (0 : ℝ)) := by
  ext y
  simp only [Set.mem_Ici, Set.mem_insert_iff, Set.mem_Ioi]
  constructor
  · intro h
    rcases eq_or_lt_of_le h with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'
  · rintro (rfl | h)
    · exact le_refl 0
    · exact le_of_lt h

/-- For a function which is `C^j` at `0`, the one-sided iterated derivative over `Ioi 0` agrees
with the ordinary iterated derivative. -/
private lemma iteratedDerivWithin_Ioi_eq_iteratedDeriv_sqrt2 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {j : ℕ} {g : ℝ → E} (hg : ContDiffAt ℝ j g 0) :
    iteratedDerivWithin j g (Set.Ioi (0 : ℝ)) 0 = iteratedDeriv j g 0 := by
  have h1 : iteratedDerivWithin j g (Set.Ioi (0 : ℝ)) 0
      = iteratedDerivWithin j g (Set.Ici (0 : ℝ)) 0 := by
    simp only [iteratedDerivWithin]
    rw [Ici_zero_eq_insert_Ioi_sqrt2, iteratedFDerivWithin_insert]
  rw [h1, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hg (by simp)]

/-! ## Extending a `C^n` function of the `τ`-variable across the seam `τ = 0`

This is `Work.RPB.B5.seamExtend` with the periodicity conclusion replaced by the σ-flatness of
the extension; the proof is that of `seamExtend` (the finite Seeley reflection
`Σ_j a_j h(c_j τ, t, σ)` glued to `h` across `τ = 0` by
`Work.RPB.B3.hasFTaylorSeriesUpToOn_of_halfspaces`), with the extra observation that the
reflected branch is a sum of `σ`-translates of `h`, so that the vanishing of the one-sided
`σ`-jets of `h` at `σ = 0` is inherited by the extension on the whole box. -/

theorem seamExtend_noPer_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ × (ℝ × ℝ) → E) (n : ℕ) {L M ρ : ℝ}
    (hL : 0 < L) (hM : 0 < M) (hM1 : M ≤ 1) (hρ : 0 < ρ)
    (hh : ContDiffOn ℝ n h (gBoxR L M ρ))
    (hflat : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ j : ℕ, j ≤ n →
      iteratedDerivWithin j (fun σ : ℝ => h (τ, t, σ)) (Set.Ioi (0 : ℝ)) 0 = 0) :
    ∃ F : ℝ × (ℝ × ℝ) → E,
      ContDiffOn ℝ n F (gBox L M ρ) ∧
      (∀ z, z ∈ gBoxR L M ρ → F z = h z) ∧
      (∀ τ t : ℝ, τ ∈ Set.Ioo (-L) M → ∀ j : ℕ, j ≤ n →
        iteratedDeriv j (fun σ : ℝ => F (τ, t, σ)) 0 = 0) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hML : (0 : ℝ) < M / L := div_pos hM hL
  let nod : Fin (n + 1) → ℝ := fun j => -((M / L) / (2 * ((n : ℝ) + 1))) * ((j : ℝ) + 1)
  have hnodval : ∀ j, nod j = -((M / L) / (2 * ((n : ℝ) + 1))) * ((j : ℝ) + 1) := fun j => rfl
  have hc0 : (0 : ℝ) < (M / L) / (2 * ((n : ℝ) + 1)) := by positivity
  have hs_lt : ∀ j, nod j < 0 := by
    intro j
    rw [hnodval j]
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    nlinarith [hc0, hj]
  have hs_inj : Function.Injective nod := by
    intro i j hij
    rw [hnodval i, hnodval j] at hij
    have hsum : ((i : ℝ) + 1) = ((j : ℝ) + 1) :=
      mul_left_cancel₀ (ne_of_gt hc0) (by linarith [hij])
    exact Fin.ext (by exact_mod_cast (by linarith [hsum] : (i : ℝ) = (j : ℝ)))
  have hbound : ∀ j, M / nod j = -L * (2 * ((n : ℝ) + 1) / ((j : ℝ) + 1)) := by
    intro j
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hMne : M ≠ 0 := ne_of_gt hM
    have hLne : L ≠ 0 := ne_of_gt hL
    have hnne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hnpos
    rw [hnodval j]
    field_simp
  have hcL : ∀ j, M / nod j ≤ -L := by
    intro j
    rw [hbound j]
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hle : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) / ((j : ℝ) + 1) := by
      rw [le_div_iff₀ hj1]
      have hjn : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have h : (j : ℕ) + 1 ≤ n + 1 := Nat.succ_le_iff.mpr j.isLt
        exact_mod_cast h
      nlinarith [hjn, hnpos]
    nlinarith [hle, hL]
  obtain ⟨a, ha⟩ := Work.RPB.B5.existsSeeleyWeights n nod hs_inj
  have hid : ∀ m : ℕ, m ≤ n → ∑ j, a j * (nod j) ^ m = 1 := fun m hm =>
    ha ⟨m, Nat.lt_succ_of_le hm⟩
  have hsum1 : ∑ j, a j = 1 := by
    have := ha 0
    simpa using this
  let G : ℝ × (ℝ × ℝ) → E := fun z => ∑ j, a j • h (Work.RPB.B3.reflLin (nod j) z)
  have hG : ContDiffOn ℝ n G (gBoxL L M ρ) := by
    refine ContDiffOn.sum (f := fun j z => a j • h (Work.RPB.B3.reflLin (nod j) z)) ?_
    intro j _
    exact (((hh.comp_continuousLinearMap (Work.RPB.B3.reflLin (nod j))).mono
      (gBoxL_subset_preimage hL (hs_lt j) (hcL j))).const_smul (a j))
  let F : ℝ × (ℝ × ℝ) → E := fun z => if z.1 ≤ 0 then G z else h z
  have hFeqR : ∀ z ∈ gBoxR L M ρ, F z = h z := by
    intro z hz
    show (if z.1 ≤ 0 then G z else h z) = h z
    by_cases hlt : z.1 ≤ 0
    · rw [if_pos hlt]
      have hz0 : z.1 = 0 := le_antisymm hlt hz.2
      show (∑ j, a j • h (Work.RPB.B3.reflLin (nod j) z)) = h z
      have hzj : ∀ j, Work.RPB.B3.reflLin (nod j) z = z := fun j => by
        obtain ⟨τ, s', r⟩ := z
        simp only at hz0
        simp [Work.RPB.B3.reflLin_apply, hz0]
      simp only [hzj, ← Finset.sum_smul, hsum1, one_smul]
    · rw [if_neg hlt]
  have hFeqL : ∀ z ∈ gBoxL L M ρ, F z = G z := fun z hz => by
    have hzle : z.1 ≤ 0 := hz.2
    show (if z.1 ≤ 0 then G z else h z) = G z
    rw [if_pos hzle]
  have hjetG := hG.ftaylorSeriesWithin (uniqueDiffOn_gBoxL hL hM hρ)
  have hjetH := hh.ftaylorSeriesWithin (uniqueDiffOn_gBoxR hL hM hρ)
  let p : ℝ × (ℝ × ℝ) → FormalMultilinearSeries ℝ (ℝ × (ℝ × ℝ)) E :=
    fun z => if z.1 ≤ 0 then ftaylorSeriesWithin ℝ G (gBoxL L M ρ) z
             else ftaylorSeriesWithin ℝ h (gBoxR L M ρ) z
  have hpval : ∀ z, p z = (if z.1 ≤ 0 then ftaylorSeriesWithin ℝ G (gBoxL L M ρ) z
             else ftaylorSeriesWithin ℝ h (gBoxR L M ρ) z) := fun z => rfl
  have hFL : HasFTaylorSeriesUpToOn (n : WithTop ENat) F p (gBoxL L M ρ) := by
    refine (hjetG.congr hFeqL).congr_series (fun m hm => fun z hz => ?_)
    have hzle : z.1 ≤ 0 := hz.2
    show ftaylorSeriesWithin ℝ G (gBoxL L M ρ) z m = p z m
    rw [hpval z, if_pos hzle]
  have hFR : HasFTaylorSeriesUpToOn (n : WithTop ENat) F p (gBoxR L M ρ) := by
    refine (hjetH.congr hFeqR).congr_series (fun m hm => fun z hz => ?_)
    show ftaylorSeriesWithin ℝ h (gBoxR L M ρ) z m = p z m
    rw [hpval z]
    by_cases hlt : z.1 ≤ 0
    · rw [if_pos hlt]
      have hz0 : z.1 = 0 := le_antisymm hlt hz.2
      have hzbox : z ∈ gBox L M ρ := hz.1
      show iteratedFDerivWithin ℝ m h (gBoxR L M ρ) z
        = iteratedFDerivWithin ℝ m G (gBoxL L M ρ) z
      exact (gTauJetMatchR h n hL hM hρ hh nod a hs_lt hcL hid z hzbox hz0 m
        (by exact_mod_cast hm)).symm
    · rw [if_neg hlt]
  refine ⟨F, (Work.RPB.B3.hasFTaylorSeriesUpToOn_of_halfspaces F n
    (isOpen_gBox L M ρ) hFL hFR).contDiffOn, hFeqR, ?_⟩
  -- the σ-jets of the extension vanish
  have hnodL : ∀ i : Fin (n + 1), -(nod i) * L = M * ((i : ℝ) + 1) / (2 * ((n : ℝ) + 1)) := by
    intro i
    have hLne : L ≠ 0 := ne_of_gt hL
    have hn1 : (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
    rw [hnodval i]
    field_simp
  have hb2 : ∀ i : Fin (n + 1), -(nod i) * L ≤ M / 2 := by
    intro i
    rw [hnodL i]
    have hile : ((i : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have h : (i : ℕ) + 1 ≤ n + 1 := Nat.succ_le_iff.mpr i.isLt
      exact_mod_cast h
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))]
    nlinarith [hile, hM]
  -- smoothness of the σ-slice of `h` at the reflected points
  have hslice_smooth : ∀ (c' t' : ℝ), c' ∈ Set.Ioo (-L) M → 0 ≤ c' →
      ContDiffAt ℝ n (fun σ : ℝ => h (c', t', σ)) 0 := by
    intro c' t' hc' hc'0
    have hpt : (c', t', 0) ∈ gBoxR L M ρ :=
      Work.RPB.B5.mem_gBoxR.mpr ⟨⟨hc', ⟨by linarith [hρ], hρ⟩⟩, hc'0⟩
    have hcd : ContDiffWithinAt ℝ n (fun σ : ℝ => h (c', t', σ)) (Set.Ioo (-ρ) ρ) 0 := by
      have hφ : ContDiffWithinAt ℝ n (fun σ : ℝ => (c', t', σ)) (Set.Ioo (-ρ) ρ) 0 :=
        (by fun_prop : ContDiff ℝ n (fun σ : ℝ => (c', t', σ))).contDiffWithinAt
      have hmap : Set.MapsTo (fun σ : ℝ => (c', t', σ)) (Set.Ioo (-ρ) ρ) (gBoxR L M ρ) :=
        fun σ hσ => Work.RPB.B5.mem_gBoxR.mpr ⟨⟨hc', hσ⟩, hc'0⟩
      have h := (hh.contDiffWithinAt hpt).comp 0 hφ hmap
      simpa only [Function.comp_def] using h
    exact hcd.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [hρ], hρ⟩)
  intro τ t hτbox j hj
  by_cases hτle : τ ≤ 0
  · have hFG : ∀ σ : ℝ, F (τ, t, σ) = ∑ i, a i • h (nod i * τ, t, σ) := by
      intro σ
      show (if τ ≤ 0 then G (τ, t, σ) else h (τ, t, σ)) = _
      rw [if_pos hτle]
      simp only [G, Work.RPB.B3.reflLin_apply]
    have hcnn : ∀ i, 0 ≤ nod i * τ := fun i => by nlinarith [hs_lt i, hτle]
    have hc1 : ∀ i, nod i * τ ≤ 1 := fun i => by
      have h1 : nod i * τ ≤ -(nod i) * L := by nlinarith [hs_lt i, hτbox.1, hτle]
      have h2 : -(nod i) * L ≤ M / 2 := hb2 i
      linarith [hM1]
    have hτmem : ∀ i, nod i * τ ∈ Set.Ioo (-L) M := fun i => by
      refine ⟨by linarith [hcnn i, hL], ?_⟩
      have h1 : nod i * τ ≤ -(nod i) * L := by nlinarith [hs_lt i, hτbox.1, hτle]
      linarith [h1, hb2 i, hM]
    have hiter : iteratedDeriv j (fun σ : ℝ => F (τ, t, σ)) 0
        = ∑ i, a i • iteratedDeriv j (fun σ : ℝ => h (nod i * τ, t, σ)) 0 := by
      rw [show (fun σ : ℝ => F (τ, t, σ))
          = (fun σ : ℝ => ∑ i, a i • h (nod i * τ, t, σ)) from funext hFG]
      have hsum := iteratedDeriv_fun_sum (x := (0 : ℝ)) (n := j)
        (f := fun i : Fin (n + 1) => fun σ : ℝ => a i • h (nod i * τ, t, σ))
        (I := Finset.univ) (fun i _ =>
          ((hslice_smooth (nod i * τ) t (hτmem i) (hcnn i)).of_le
            (by exact_mod_cast hj)).const_smul (a i))
      rw [hsum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact iteratedDeriv_const_smul (f := fun σ : ℝ => h (nod i * τ, t, σ))
        ((hslice_smooth (nod i * τ) t (hτmem i) (hcnn i)).of_le (by exact_mod_cast hj)) (a i)
    rw [hiter]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [show iteratedDeriv j (fun σ : ℝ => h (nod i * τ, t, σ)) 0 = 0 from ?_, smul_zero]
    rw [← iteratedDerivWithin_Ioi_eq_iteratedDeriv_sqrt2
      ((hslice_smooth (nod i * τ) t (hτmem i) (hcnn i)).of_le (by exact_mod_cast hj))]
    exact hflat (nod i * τ) ⟨hcnn i, hc1 i⟩ t j hj
  · push_neg at hτle
    have hFh : ∀ σ : ℝ, F (τ, t, σ) = h (τ, t, σ) := by
      intro σ
      show (if τ ≤ 0 then G (τ, t, σ) else h (τ, t, σ)) = h (τ, t, σ)
      rw [if_neg (not_le.mpr hτle)]
    have hτmem : τ ∈ Set.Ioo (-L) M := ⟨hτbox.1, hτbox.2⟩
    rw [show (fun σ : ℝ => F (τ, t, σ)) = (fun σ : ℝ => h (τ, t, σ)) from funext hFh]
    rw [← iteratedDerivWithin_Ioi_eq_iteratedDeriv_sqrt2
      ((hslice_smooth τ t hτmem (le_of_lt hτle)).of_le (by exact_mod_cast hj))]
    exact hflat τ ⟨le_of_lt hτle, by linarith [hτbox.2, hM1]⟩ t j hj

/-! ## Flat truncation on the `τ`-slab -/

/-- **Flat truncation on the slab.**  If `h(τ,t,σ)` is `C^k` on the slab `[0,1] × ℝ × (-c,c)` and
all its one-sided `σ`-jets at `σ = 0` vanish (for `τ ∈ [0,1]`), then the truncation
`(τ,t,σ) ↦ if σ ≤ 0 then 0 else h(τ,t,σ)` is `C^k` within `[0,1] × ℝ × ℝ` at `(τ₀, (t₀, 0))`.

The `τ ∈ [0,1]`-restriction of the data is removed by extending `h` across the seams `τ = 0` and
`τ = 1` (the latter after the substitution `τ ↦ 1 - τ`) by `seamExtend_noPer_local`; the σ-jets of
those extensions still vanish, so `contDiff_piecewise_param` glues `0` and the (compactly
cut-off) extension across `σ = 0`. -/
theorem flatTrunc_slab_point_local (k : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → ℝ → ℝ → E) (τ₀ t₀ : ℝ) (c : ℝ) (hc : 0 < c)
    (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1)
    (hsm : ContDiffOn ℝ k (fun z : ℝ × (ℝ × ℝ) => h z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c))
    (hflat : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ j : ℕ, j ≤ k →
      iteratedDerivWithin j (fun σ : ℝ => h τ t σ) (Set.Ioi (0 : ℝ)) 0 = 0) :
    ContDiffWithinAt ℝ k (fun z : ℝ × (ℝ × ℝ) => if z.2.2 ≤ 0 then 0 else h z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (t₀, 0)) := by
  classical
  -- the box function and its two extensions in `τ`
  set hB : ℝ × (ℝ × ℝ) → E := fun z => h z.1 z.2.1 z.2.2 with hhB
  have hhBR : ContDiffOn ℝ k hB (gBoxR 1 (3 / 4) c) := by
    rw [hhB]
    refine hsm.mono ?_
    intro z hz
    rw [Work.RPB.B5.mem_gBoxR] at hz
    exact ⟨⟨hz.2, by linarith [hz.1.1.2]⟩, trivial, hz.1.2⟩
  have hflatB : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ j : ℕ, j ≤ k →
      iteratedDerivWithin j (fun σ : ℝ => hB (τ, t, σ)) (Set.Ioi (0 : ℝ)) 0 = 0 := by
    intro τ hτ t j hj
    simpa only [hhB] using hflat τ hτ t j hj
  obtain ⟨F, hFcd, hFeq, hFjet⟩ :=
    seamExtend_noPer_local hB k (by norm_num) (by norm_num) (by norm_num) hc hhBR hflatB
  set hB' : ℝ × (ℝ × ℝ) → E := fun z => hB (1 - z.1, z.2.1, z.2.2) with hhB'
  have hhB'R : ContDiffOn ℝ k hB' (gBoxR 1 (3 / 4) c) := by
    rw [hhB']
    have hφ : ContDiffOn ℝ k (fun z : ℝ × (ℝ × ℝ) => (1 - z.1, z.2.1, z.2.2))
        (gBoxR 1 (3 / 4) c) := by fun_prop
    have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (1 - z.1, z.2.1, z.2.2)) (gBoxR 1 (3 / 4) c)
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) := by
      intro z hz
      rw [Work.RPB.B5.mem_gBoxR] at hz
      exact ⟨⟨by linarith [hz.1.1.2], by linarith [hz.2]⟩, trivial, hz.1.2⟩
    have h := hsm.comp hφ hmap
    simpa only [hhB, Function.comp_def] using h
  have hflatB' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ j : ℕ, j ≤ k →
      iteratedDerivWithin j (fun σ : ℝ => hB' (τ, t, σ)) (Set.Ioi (0 : ℝ)) 0 = 0 := by
    intro τ hτ t j hj
    have h1 : (fun σ : ℝ => hB' (τ, t, σ)) = (fun σ : ℝ => hB (1 - τ, t, σ)) := by
      funext σ; simp only [hhB']
    rw [h1]
    exact hflatB (1 - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩ t j hj
  obtain ⟨F', hF'cd, hF'eq, hF'jet⟩ :=
    seamExtend_noPer_local hB' k (by norm_num) (by norm_num) (by norm_num) hc hhB'R hflatB'
  -- the ambient piecewise function
  set Famb : ℝ × (ℝ × ℝ) → E :=
    fun z => if z.1 ≤ 1 / 2 then F z else F' (1 - z.1, z.2.1, z.2.2) with hFamb
  have hFambF : ∀ z ∈ ((Set.Ioo (-1) (3 / 4) : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c
      : Set (ℝ × (ℝ × ℝ))), Famb z = F z := by
    intro z hz
    simp only [hFamb]
    by_cases hh12 : z.1 ≤ 1 / 2
    · rw [if_pos hh12]
    · rw [if_neg hh12]
      have h2 : (1 - z.1, z.2.1, z.2.2) ∈ gBoxR 1 (3 / 4) c :=
        Work.RPB.B5.mem_gBoxR.mpr ⟨⟨⟨by linarith [hz.1.2], by linarith [hh12]⟩, hz.2.2⟩,
          by linarith [hz.1.2]⟩
      have h3 : z ∈ gBoxR 1 (3 / 4) c :=
        Work.RPB.B5.mem_gBoxR.mpr ⟨⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2.2⟩,
          by linarith [hz.1.1]⟩
      rw [hF'eq _ h2, hFeq _ h3]
      simp only [hhB', hhB]
      congr 1
      ring
  have hFambF_cd : ContDiffOn ℝ k Famb
      ((Set.Ioo (-1) (3 / 4) : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) := hFcd.congr hFambF
  have hFambF' : ∀ z ∈ ((Set.Ioo (1 / 4) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c
      : Set (ℝ × (ℝ × ℝ))), Famb z = F' (1 - z.1, z.2.1, z.2.2) := by
    intro z hz
    simp only [hFamb]
    by_cases hh12 : z.1 ≤ 1 / 2
    · rw [if_pos hh12]
      have h2 : (1 - z.1, z.2.1, z.2.2) ∈ gBoxR 1 (3 / 4) c :=
        Work.RPB.B5.mem_gBoxR.mpr ⟨⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, hz.2.2⟩,
          by linarith [hh12]⟩
      have h3 : z ∈ gBoxR 1 (3 / 4) c :=
        Work.RPB.B5.mem_gBoxR.mpr ⟨⟨⟨by linarith [hz.1.1], by linarith⟩, hz.2.2⟩,
          by linarith [hz.1.1]⟩
      rw [hF'eq _ h2, hFeq _ h3]
      simp only [hhB', hhB]
      congr 1
      ring
    · rw [if_neg hh12]
  have hFambF'_cd : ContDiffOn ℝ k (fun z : ℝ × (ℝ × ℝ) => F' (1 - z.1, z.2.1, z.2.2))
      ((Set.Ioo (1 / 4) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) := by
    have hφ : ContDiffOn ℝ k (fun z : ℝ × (ℝ × ℝ) => (1 - z.1, z.2.1, z.2.2))
        ((Set.Ioo (1 / 4) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) := by fun_prop
    have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (1 - z.1, z.2.1, z.2.2))
        ((Set.Ioo (1 / 4) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) (gBox 1 (3 / 4) c) := by
      intro z hz
      rw [Work.RPB.B5.mem_gBox]
      exact ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, hz.2.2⟩
    exact hF'cd.comp hφ hmap
  have hFamb_cd2 : ContDiffOn ℝ k Famb ((Set.Ioo (1 / 4) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) :=
    hFambF'_cd.congr hFambF'
  have hFamb_cd : ContDiffOn ℝ k Famb ((Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) := by
    refine contDiffOn_of_locally_contDiffOn (fun z hz => ?_)
    by_cases hh34 : z.1 < 3 / 4
    · exact ⟨(Set.Ioo (-1) (3 / 4) : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c,
        isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo),
        ⟨⟨hz.1.1, hh34⟩, trivial, hz.2.2⟩,
        hFambF_cd.mono Set.inter_subset_right⟩
    · push_neg at hh34
      exact ⟨(Set.Ioo (1 / 4) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c,
        isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo),
        ⟨⟨by linarith, hz.1.2⟩, trivial, hz.2.2⟩,
        hFamb_cd2.mono Set.inter_subset_right⟩
  have hFamb_jet : ∀ (τ t : ℝ), τ ∈ Set.Ioo (-1) 2 → ∀ j : ℕ, j ≤ k →
      iteratedDeriv j (fun σ : ℝ => Famb (τ, t, σ)) 0 = 0 := by
    intro τ t hτ j hj
    by_cases hh12 : τ ≤ 1 / 2
    · have hfun : (fun σ : ℝ => Famb (τ, t, σ)) = (fun σ : ℝ => F (τ, t, σ)) := by
        funext σ; simp only [hFamb]; rw [if_pos hh12]
      rw [hfun]
      exact hFjet τ t ⟨hτ.1, by linarith⟩ j hj
    · push_neg at hh12
      have hfun : (fun σ : ℝ => Famb (τ, t, σ)) = (fun σ : ℝ => F' (1 - τ, t, σ)) := by
        funext σ; simp only [hFamb]; rw [if_neg (not_le.mpr hh12)]
      rw [hfun]
      exact hF'jet (1 - τ) t ⟨by linarith [hτ.2], by linarith⟩ j hj
  -- the cut-off in `τ` and in `σ`
  set βc : ℝ → ℝ := fun τ => Real.smoothTransition (2 * τ + 1) * Real.smoothTransition (3 - 2 * τ)
    with hβc
  have hβc_cd : ContDiff ℝ k βc := by
    rw [hβc]
    exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop))
  have hβsupp : ∀ τ : ℝ, βc τ ≠ 0 → τ ∈ Set.Ioo (-1) 2 := by
    intro τ hτ
    constructor
    · by_contra hle
      push_neg at hle
      exact hτ (by simp only [hβc]; rw [Real.smoothTransition.zero_of_nonpos
        (show 2 * τ + 1 ≤ 0 by linarith), zero_mul])
    · by_contra hle
      push_neg at hle
      exact hτ (by simp only [hβc]; rw [Real.smoothTransition.zero_of_nonpos
        (show 3 - 2 * τ ≤ 0 by linarith), mul_zero])
  set ψv : ℝ → ℝ :=
    fun σ => Real.smoothTransition (4 * σ / c + 2) * Real.smoothTransition (2 - 4 * σ / c)
    with hψv
  have hψv_cd : ContDiff ℝ k ψv := by
    rw [hψv]
    exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop))
  have hψv_one : ∀ σ : ℝ, |σ| ≤ c / 4 → ψv σ = 1 := by
    intro σ hσ
    have hσ1 : -(c / 4) ≤ σ := (abs_le.mp hσ).1
    have hσ2 : σ ≤ c / 4 := (abs_le.mp hσ).2
    have h4 : (-1 : ℝ) ≤ 4 * σ / c := (le_div_iff₀ hc).mpr (by linarith)
    have h4' : 4 * σ / c ≤ 1 := (div_le_iff₀ hc).mpr (by linarith)
    simp only [hψv]
    rw [Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 4 * σ / c + 2),
      Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ 2 - 4 * σ / c), mul_one]
  -- `A := βc · ψv`
  set A : ℝ × (ℝ × ℝ) → ℝ := fun z => βc z.1 * ψv z.2.2 with hA
  have hA_cd : ContDiff ℝ k A := by
    rw [hA]
    exact (hβc_cd.comp contDiff_fst).mul (hψv_cd.comp contDiff_snd.snd)
  have hA_one : ∀ z : ℝ × (ℝ × ℝ), z.1 ∈ Set.Icc (0 : ℝ) 1 → |z.2.2| ≤ c / 4 → A z = 1 := by
    intro z hz hzσ
    have hβ1 : βc z.1 = 1 := by
      simp only [hβc]
      rw [Real.smoothTransition.one_of_one_le (by linarith [hz.1] : (1 : ℝ) ≤ 2 * z.1 + 1),
        Real.smoothTransition.one_of_one_le (by linarith [hz.2] : (1 : ℝ) ≤ 3 - 2 * z.1),
        mul_one]
    simp only [hA, hβ1, hψv_one z.2.2 hzσ, one_mul]
  have hA_zero : ∀ z, z ∉ (Set.Icc (-(1 / 2) : ℝ) (3 / 2) ×ˢ (Set.univ : Set ℝ)
      ×ˢ Set.Icc (-(3 * c / 4)) (3 * c / 4)) → A z = 0 := by
    intro z hz
    by_contra hne
    apply hz
    have hβ : βc z.1 ≠ 0 := fun h0 => hne (by simp only [hA]; rw [h0, zero_mul])
    have hψ : ψv z.2.2 ≠ 0 := fun h0 => hne (by simp only [hA]; rw [h0, mul_zero])
    have h1 : -(1 / 2 : ℝ) < z.1 := by
      by_contra hle
      push_neg at hle
      exact hβ (by simp only [hβc]; rw [Real.smoothTransition.zero_of_nonpos
        (show 2 * z.1 + 1 ≤ 0 by linarith), zero_mul])
    have h2 : z.1 < 3 / 2 := by
      by_contra hle
      push_neg at hle
      exact hβ (by simp only [hβc]; rw [Real.smoothTransition.zero_of_nonpos
        (show 3 - 2 * z.1 ≤ 0 by linarith), mul_zero])
    have h3 : z.2.2 ∈ Set.Icc (-(3 * c / 4)) (3 * c / 4) := by
      have hlo : -(c / 2) < z.2.2 := by
        by_contra hle
        push_neg at hle
        refine hψ (?_)
        simp only [hψv]
        have hx : 4 * z.2.2 / c + 2 ≤ 0 := by
          have h1 : 4 * z.2.2 ≤ (-2 : ℝ) * c := by linarith
          have h2 : 4 * z.2.2 / c ≤ (-2 : ℝ) := (div_le_iff₀ hc).mpr h1
          linarith
        rw [Real.smoothTransition.zero_of_nonpos hx, zero_mul]
      have hhi : z.2.2 < c / 2 := by
        by_contra hle
        push_neg at hle
        refine hψ (?_)
        simp only [hψv]
        have hx : 2 - 4 * z.2.2 / c ≤ 0 := by
          have h1 : (2 : ℝ) * c ≤ 4 * z.2.2 := by linarith
          have h2 : (2 : ℝ) ≤ 4 * z.2.2 / c := (le_div_iff₀ hc).mpr h1
          linarith
        rw [Real.smoothTransition.zero_of_nonpos hx, mul_zero]
      exact ⟨le_of_lt (by linarith), le_of_lt (by linarith)⟩
    exact ⟨⟨le_of_lt h1, le_of_lt h2⟩, trivial, h3⟩
  set G : ℝ × (ℝ × ℝ) → E := fun z => A z • Famb z with hG
  have hUopen : IsOpen ((Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) :=
    isOpen_Ioo.prod ((isOpen_univ : IsOpen (Set.univ : Set ℝ)).prod isOpen_Ioo)
  have hG_cd : ContDiff ℝ k G := by
    have hBclosed : IsClosed (Set.Icc (-(1 / 2) : ℝ) (3 / 2) ×ˢ (Set.univ : Set ℝ)
        ×ˢ Set.Icc (-(3 * c / 4)) (3 * c / 4)) :=
      isClosed_Icc.prod ((isClosed_univ : IsClosed (Set.univ : Set ℝ)).prod isClosed_Icc)
    have hBU : (Set.Icc (-(1 / 2) : ℝ) (3 / 2) ×ˢ (Set.univ : Set ℝ)
        ×ˢ Set.Icc (-(3 * c / 4)) (3 * c / 4))
        ⊆ ((Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) := by
      intro z hz
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, trivial,
        ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩⟩
    have hVopen : IsOpen ((Set.Icc (-(1 / 2) : ℝ) (3 / 2) ×ˢ (Set.univ : Set ℝ)
        ×ˢ Set.Icc (-(3 * c / 4)) (3 * c / 4))ᶜ) := hBclosed.isOpen_compl
    have hGU : ContDiffOn ℝ k G ((Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) := by
      rw [hG]
      exact (hA_cd.contDiffOn.mono (Set.subset_univ _)).smul hFamb_cd
    have hGV : ContDiffOn ℝ k G ((Set.Icc (-(1 / 2) : ℝ) (3 / 2) ×ˢ (Set.univ : Set ℝ)
        ×ˢ Set.Icc (-(3 * c / 4)) (3 * c / 4))ᶜ) := by
      rw [hG]
      refine (contDiffOn_const : ContDiffOn ℝ k (fun _ : ℝ × (ℝ × ℝ) => (0 : E))
        ((Set.Icc (-(1 / 2) : ℝ) (3 / 2) ×ˢ (Set.univ : Set ℝ)
          ×ˢ Set.Icc (-(3 * c / 4)) (3 * c / 4))ᶜ)).congr ?_
      intro z hz
      rw [hA_zero z hz, zero_smul]
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ ((Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c)
    · have hzu : ((Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) ∈ 𝓝 z :=
        hUopen.mem_nhds hz
      exact hGU.contDiffAt hzu
    · refine hGV.contDiffAt (hVopen.mem_nhds ?_)
      simp only [Set.mem_compl_iff]
      intro hb
      exact hz (hBU hb)
  -- the σ-jets of `G` vanish everywhere
  have hjetG : ∀ p : ℝ × ℝ, ∀ j : ℕ, j ≤ k →
      iteratedDeriv j (fun σ : ℝ => G (p.1, p.2, σ)) 0 = 0 := by
    intro p j hj
    by_cases hβ : βc p.1 = 0
    · have hzero : (fun σ : ℝ => G (p.1, p.2, σ)) = fun _ => (0 : E) := by
        funext σ
        simp only [hG, hA]
        rw [hβ, zero_mul, zero_smul]
      rw [hzero, iteratedDeriv_const]
      split <;> rfl
    · have hτmem : p.1 ∈ Set.Ioo (-1) 2 := hβsupp p.1 hβ
      have hptU : (p.1, p.2, 0) ∈
          ((Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) := by
        refine ⟨?_, ?_, ?_⟩
        · exact hτmem
        · exact trivial
        · exact ⟨by linarith [hc], hc⟩
      have hptUn : ((Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-c) c) ∈
          𝓝 (p.1, p.2, 0) := hUopen.mem_nhds hptU
      have hFamb_at : ContDiffAt ℝ k Famb (p.1, p.2, 0) := hFamb_cd.contDiffAt hptUn
      have hslice : ContDiffAt ℝ k (fun σ : ℝ => Famb (p.1, p.2, σ)) 0 := by
        have hinner : ContDiffAt ℝ k (fun σ : ℝ => (p.1, p.2, σ)) 0 := by fun_prop
        have hcomp := ContDiffAt.comp (x := (0 : ℝ)) (f := fun σ : ℝ => (p.1, p.2, σ))
          (g := Famb) hFamb_at hinner
        simpa only [Function.comp_def] using hcomp
      have hprod : ContDiffAt ℝ k (fun σ : ℝ => ψv σ • Famb (p.1, p.2, σ)) 0 :=
        (hψv_cd.contDiffAt).smul hslice
      have hev : (fun σ : ℝ => ψv σ • Famb (p.1, p.2, σ))
          =ᶠ[𝓝 (0 : ℝ)] (fun σ : ℝ => Famb (p.1, p.2, σ)) := by
        have hmem : {σ : ℝ | |σ| ≤ c / 4} ∈ 𝓝 (0 : ℝ) := by
          refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0:ℝ) < c/4)) ?_
          intro σ hσ
          rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hσ
          exact le_of_lt hσ
        filter_upwards [hmem] with σ hσ
        rw [hψv_one σ hσ, one_smul]
      have h1 : iteratedDeriv j (fun σ : ℝ => ψv σ • Famb (p.1, p.2, σ)) 0
          = iteratedDeriv j (fun σ : ℝ => Famb (p.1, p.2, σ)) 0 := hev.iteratedDeriv_eq j
      have h2 : iteratedDeriv j (fun σ : ℝ => Famb (p.1, p.2, σ)) 0 = 0 :=
        hFamb_jet p.1 p.2 hτmem j hj
      have hfun : (fun σ : ℝ => G (p.1, p.2, σ)) = (βc p.1) •
          (fun σ : ℝ => ψv σ • Famb (p.1, p.2, σ)) := by
        funext σ
        simp only [hG, hA, mul_smul, Pi.smul_apply]
      rw [hfun, iteratedDeriv_const_smul (f := fun σ : ℝ => ψv σ • Famb (p.1, p.2, σ))
        (hprod.of_le (by exact_mod_cast hj)) (βc p.1), h1, h2, smul_zero]
  -- glue `0` and `G` across `σ = 0`
  have hpiece : ContDiff ℝ k
      (fun z : (ℝ × ℝ) × ℝ => if z.2 ≤ 0 then (0 : E) else G (z.1.1, z.1.2, z.2)) := by
    refine contDiff_piecewise_param k (fun _ : ℝ × ℝ => fun _ : ℝ => (0 : E))
      (fun p : ℝ × ℝ => fun σ : ℝ => G (p.1, p.2, σ)) 0 contDiff_const ?_ ?_
    · have he : ContDiff ℝ k (fun z : (ℝ × ℝ) × ℝ =>
          (LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ ℝ) z) :=
        (LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ ℝ).toContinuousLinearEquiv.contDiff
      have h1 := hG_cd.comp he
      have h2 : (G ∘ (fun z : (ℝ × ℝ) × ℝ => (LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ ℝ) z))
          = (fun z : (ℝ × ℝ) × ℝ => G (z.1.1, z.1.2, z.2)) := by
        funext z
        rcases z with ⟨⟨a, b⟩, cc⟩
        simp
      rw [h2] at h1
      exact h1
    · intro p j hj
      have h0 : iteratedDeriv j (fun _ : ℝ => (0 : E)) 0 = 0 := by
        rw [iteratedDeriv_const]
        split <;> rfl
      rw [h0]
      exact (hjetG p j hj).symm
  have hpiece' : ContDiff ℝ k
      (fun w : ℝ × (ℝ × ℝ) => if w.2.2 ≤ 0 then (0 : E) else G (w.1, w.2.1, w.2.2)) := by
    have he : ContDiff ℝ k (fun w : ℝ × (ℝ × ℝ) =>
        (LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm w) :=
      (LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm.toContinuousLinearEquiv.contDiff
    have h1 := hpiece.comp he
    have h2 : ((fun z : (ℝ × ℝ) × ℝ => if z.2 ≤ 0 then (0 : E) else G (z.1.1, z.1.2, z.2)) ∘
        (fun w : ℝ × (ℝ × ℝ) => (LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm w))
        = (fun w : ℝ × (ℝ × ℝ) => if w.2.2 ≤ 0 then (0 : E) else G (w.1, w.2.1, w.2.2)) := by
      funext w
      rcases w with ⟨a, b, cc⟩
      simp
    rw [h2] at h1
    exact h1
  -- the agreement of the two truncations near the point
  have hFamb_h : ∀ (τ t σ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → |σ| < c → Famb (τ, t, σ) = h τ t σ := by
    intro τ t σ hτ hσ
    have hσmem : σ ∈ Set.Ioo (-c) c :=
      ⟨by have := (abs_lt.mp hσ).1; linarith, by have := (abs_lt.mp hσ).2; linarith⟩
    by_cases hh12 : τ ≤ 1 / 2
    · have hz : (τ, t, σ) ∈ gBoxR 1 (3 / 4) c :=
        Work.RPB.B5.mem_gBoxR.mpr ⟨⟨⟨by linarith [hτ.1], by linarith [hh12]⟩, hσmem⟩, hτ.1⟩
      simp only [hFamb]
      rw [if_pos hh12, hFeq _ hz, hhB]
    · push_neg at hh12
      have hz : (1 - τ, t, σ) ∈ gBoxR 1 (3 / 4) c :=
        Work.RPB.B5.mem_gBoxR.mpr ⟨⟨⟨by linarith [hτ.2], by linarith [hh12]⟩, hσmem⟩,
          by linarith [hτ.2]⟩
      simp only [hFamb]
      rw [if_neg (not_le.mpr hh12), hF'eq _ hz]
      simp only [hhB', hhB]
      congr 1
      ring
  set S : Set (ℝ × (ℝ × ℝ)) :=
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ : Set (ℝ × (ℝ × ℝ))) with hSdef
  have hpt : (τ₀, (t₀, 0)) ∈ S := ⟨hτ₀, trivial, trivial⟩
  have heq : (fun w : ℝ × (ℝ × ℝ) => if w.2.2 ≤ 0 then (0 : E) else h w.1 w.2.1 w.2.2)
      =ᶠ[𝓝[S] (τ₀, (t₀, 0))]
      (fun w : ℝ × (ℝ × ℝ) => if w.2.2 ≤ 0 then (0 : E) else G (w.1, w.2.1, w.2.2)) := by
    have hmem : {w : ℝ × (ℝ × ℝ) | |w.2.2| < c / 4} ∈ 𝓝 (τ₀, (t₀, 0)) := by
      refine (isOpen_lt (continuous_abs.comp (continuous_snd.comp continuous_snd))
        continuous_const).mem_nhds ?_
      show |(0 : ℝ)| < c / 4
      rw [abs_zero]
      linarith
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hmem] with w hwS hwσ
    have hτ : w.1 ∈ Set.Icc (0 : ℝ) 1 := hwS.1
    have hFh : G (w.1, w.2.1, w.2.2) = h w.1 w.2.1 w.2.2 := by
      have h1 : G (w.1, w.2.1, w.2.2) = Famb (w.1, w.2.1, w.2.2) := by
        simp only [hG]
        rw [hA_one w hτ (le_of_lt hwσ), one_smul]
      rw [h1, hFamb_h w.1 w.2.1 w.2.2 hτ (by linarith [hwσ])]
    by_cases hσ : w.2.2 ≤ 0
    · rw [if_pos hσ, if_pos hσ]
    · rw [if_neg hσ, if_neg hσ, hFh]
  exact (hpiece'.contDiffAt.contDiffWithinAt (s := S)).congr_of_eventuallyEq heq
    (heq.eq_of_nhdsWithin hpt)

theorem lagData_smooth_at_sqrt2 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (τ₀ : ℝ) (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1) (t₀ : ℝ) :
    ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (Real.sqrt 2, t₀)) := by
  set S : Set (ℝ × (ℝ × ℝ)) :=
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ : Set (ℝ × (ℝ × ℝ))) with hSdef
  -- the two profiles in the `(τ, t, σ)`-variables
  set chartP : ℝ × (ℝ × ℝ) → Work.RPV.PS :=
    fun s => D.W s.1 s.2.1 (D.ρh s.1 s.2.1 s.2.2) with hchartP
  set diffP : ℝ × (ℝ × ℝ) → Work.RPV.PS :=
    fun s => collarPt D.Γc D.Ac s.1 s.2.2 s.2.1 - D.W s.1 s.2.1 (D.ρh s.1 s.2.1 s.2.2)
    with hdiffP
  set truncP : ℝ × (ℝ × ℝ) → Work.RPV.PS :=
    fun s => if s.2.2 ≤ 0 then 0 else diffP s with htruncP
  have hsig : ContDiff ℝ 8 (fun x : ℝ => sig x) := by unfold sig; fun_prop
  have hsig0 : sig (-Real.sqrt 2) = 0 := by
    simp only [sig, neg_sq, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  -- ## the chord profile `chartP` is `C⁸`
  have hchartP_cd : ContDiffWithinAt ℝ 8 chartP S (τ₀, (t₀ - Real.pi, 0)) := by
    set T : Set (ℝ × (ℝ × ℝ)) :=
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-D.κ) D.κ : Set (ℝ × (ℝ × ℝ)))
      with hTdef
    have hTcdo : ContDiffOn ℝ 8 chartP T := by
      rw [hchartP, hTdef]; exact chartLev_W_rho_contDiffOn CI a ha D
    have hTsub : T ⊆ S := by
      rw [hTdef, hSdef]
      exact Set.prod_mono (le_refl _) (Set.prod_mono (le_refl _) (fun _ _ => trivial))
    have hTmem : T ∈ 𝓝[S] (τ₀, (t₀ - Real.pi, 0)) := by
      have hVopen : IsOpen ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-D.κ) D.κ) :=
        isOpen_univ.prod (isOpen_univ.prod isOpen_Ioo)
      have hV : ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-D.κ) D.κ)
          ∈ 𝓝 (τ₀, (t₀ - Real.pi, 0)) :=
        hVopen.mem_nhds ⟨trivial, trivial, ⟨by linarith [D.hκ], D.hκ⟩⟩
      refine Filter.mem_of_superset (inter_mem_nhdsWithin S hV) ?_
      intro z hz
      exact ⟨hz.1.1, trivial, hz.2.2.2⟩
    have hpt : (τ₀, (t₀ - Real.pi, 0)) ∈ T :=
      ⟨hτ₀, trivial, ⟨by linarith [D.hκ], D.hκ⟩⟩
    have h1 : ContDiffWithinAt ℝ 8 chartP T (τ₀, (t₀ - Real.pi, 0)) :=
      hTcdo.contDiffWithinAt hpt
    have h2 : ContDiffWithinAt ℝ 8 chartP (S ∩ T) (τ₀, (t₀ - Real.pi, 0)) := by
      rwa [Set.inter_eq_right.mpr hTsub]
    exact (contDiffWithinAt_inter' hTmem).mp h2
  -- ## the flat truncation of `collar − chart` is `C⁸`
  have hsmP : ContDiffOn ℝ 8 (fun s : ℝ × (ℝ × ℝ) =>
      collarPt D.Γc D.Ac s.1 s.2.2 s.2.1 - D.W s.1 s.2.1 (D.ρh s.1 s.2.1 s.2.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-(D.κ / 2)) (D.κ / 2)) := by
    have hc : ContDiffOn ℝ 8 (fun u : ℝ × (ℝ × ℝ) => collarPt D.Γc D.Ac u.1 u.2.1 u.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := fun u hu =>
      collarPt_contDiffWithinAt D.Γc D.Ac D.hΓsm D.hAsm D.hΓper D.hAper hu.1
    have hφ : ContDiffOn ℝ 8 (fun s : ℝ × (ℝ × ℝ) => (s.1, (s.2.2, s.2.1)))
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-(D.κ / 2)) (D.κ / 2)) := by fun_prop
    have hmap : Set.MapsTo (fun s : ℝ × (ℝ × ℝ) => (s.1, (s.2.2, s.2.1)))
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-(D.κ / 2)) (D.κ / 2))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := fun s hs => ⟨hs.1, trivial, trivial⟩
    have h1 : ContDiffOn ℝ 8 (fun s : ℝ × (ℝ × ℝ) => collarPt D.Γc D.Ac s.1 s.2.2 s.2.1)
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-(D.κ / 2)) (D.κ / 2)) :=
      hc.comp hφ hmap
    have h2 : ContDiffOn ℝ 8 (fun s : ℝ × (ℝ × ℝ) => D.W s.1 s.2.1 (D.ρh s.1 s.2.1 s.2.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-(D.κ / 2)) (D.κ / 2)) :=
      (chartLev_W_rho_contDiffOn CI a ha D).mono (fun s hs =>
        ⟨hs.1, trivial, ⟨by linarith [D.hκ, hs.2.2.1], by linarith [D.hκ, hs.2.2.2]⟩⟩)
    exact h1.sub h2
  have htrunc_cd : ContDiffWithinAt ℝ 8 truncP S (τ₀, (t₀ - Real.pi, 0)) := by
    have h := flatTrunc_slab_point_local (k := 8)
      (fun τ t σ => collarPt D.Γc D.Ac τ σ t - D.W τ t (D.ρh τ t σ)) τ₀ (t₀ - Real.pi) (D.κ / 2)
      (by linarith [D.hκ]) hτ₀ hsmP (collarChart_flat CI a ha D)
    have heq : (fun z : ℝ × (ℝ × ℝ) => if z.2.2 ≤ 0 then (0 : Work.RPV.PS) else
        (collarPt D.Γc D.Ac z.1 z.2.2 z.2.1 - D.W z.1 z.2.1 (D.ρh z.1 z.2.1 z.2.2)))
        = truncP := by
      funext z; rw [htruncP, hdiffP]
    rw [heq] at h
    simpa [hSdef] using h
  -- ## the sum of the two profiles composed with `(τ,x,t) ↦ (τ,t,sig x)`
  have hcomp : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) =>
        chartP (z.1, (z.2.2, sig z.2.1)) + truncP (z.1, (z.2.2, sig z.2.1)))
      S (τ₀, (-Real.sqrt 2, t₀ - Real.pi)) := by
    have hsumP : ContDiffWithinAt ℝ 8 (fun s : ℝ × (ℝ × ℝ) => chartP s + truncP s) S
        (τ₀, (t₀ - Real.pi, 0)) := hchartP_cd.add htrunc_cd
    have hsumP' : ContDiffWithinAt ℝ 8 (fun s : ℝ × (ℝ × ℝ) => chartP s + truncP s) S
        (τ₀, (t₀ - Real.pi, sig (-Real.sqrt 2))) := by
      simpa only [hsig0] using hsumP
    have hφcd : ContDiffWithinAt ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, sig z.2.1))) S
        (τ₀, (-Real.sqrt 2, t₀ - Real.pi)) := by
      have hcd : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, sig z.2.1))) := by
        unfold sig; fun_prop
      exact hcd.contDiffWithinAt
    have hmaps : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, sig z.2.1))) S S :=
      fun z hz => ⟨hz.1, trivial, trivial⟩
    have h := ContDiffWithinAt.comp (τ₀, (-Real.sqrt 2, t₀ - Real.pi)) hsumP' hφcd hmaps
    simpa only [Function.comp_def] using h
  -- ## congruence along `lagPt_negSqrt2_decomp`
  obtain ⟨δ, hδpos, _hδle1, hdec⟩ := lagPt_negSqrt2_decomp CI a ha D
  have hptS : (τ₀, (-Real.sqrt 2, t₀ - Real.pi)) ∈ S := ⟨hτ₀, trivial, trivial⟩
  have hlag : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2) S
      (τ₀, (-Real.sqrt 2, t₀ - Real.pi)) := by
    have heq : (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
        =ᶠ[𝓝[S] (τ₀, (-Real.sqrt 2, t₀ - Real.pi))]
        (fun z => chartP (z.1, (z.2.2, sig z.2.1)) + truncP (z.1, (z.2.2, sig z.2.1))) := by
      have hmem : {z : ℝ × (ℝ × ℝ) | |z.2.1 + Real.sqrt 2| < δ}
          ∈ 𝓝[S] (τ₀, (-Real.sqrt 2, t₀ - Real.pi)) :=
        mem_nhdsWithin_of_mem_nhds
          ((isOpen_lt (continuous_abs.comp ((continuous_fst.comp continuous_snd).add
              continuous_const)) continuous_const).mem_nhds (by simpa using hδpos))
      filter_upwards [hmem, self_mem_nhdsWithin] with z hzδ hzS
      have hτ : z.1 ∈ Set.Icc (0 : ℝ) 1 := hzS.1
      rw [hdec z.1 hτ z.2.2 z.2.1 hzδ]
      simp only [hchartP, htruncP, hdiffP]
      by_cases h0 : sig z.2.1 ≤ 0
      · rw [if_pos h0, if_pos h0]
        abel
      · rw [if_neg h0, if_neg h0]
        abel
    exact hcomp.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin hptS)
  -- ## transport to `x = +√2` by `x ↦ -x`, `t ↦ t - π` and `tau π`
  have hlag_reflect : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 (-z.2.1) (z.2.2 - Real.pi))
      S (τ₀, (Real.sqrt 2, t₀)) := by
    have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (-z.2.1, z.2.2 - Real.pi))) S S :=
      fun z hz => ⟨hz.1, trivial, trivial⟩
    have hφcd : ContDiffWithinAt ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (-z.2.1, z.2.2 - Real.pi)))
        S (τ₀, (Real.sqrt 2, t₀)) :=
      (by fun_prop :
        ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (-z.2.1, z.2.2 - Real.pi)))).contDiffWithinAt
    have h := ContDiffWithinAt.comp (τ₀, (Real.sqrt 2, t₀)) hlag hφcd hmap
    simpa only [Function.comp_def] using h
  have htau : ContDiff ℝ 8 (Work.RPV.tau Real.pi) := by unfold Work.RPV.tau; fun_prop
  have htaucomp : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPV.tau Real.pi
        (lagPt D.W D.Γc D.Ac D.rho z.1 (-z.2.1) (z.2.2 - Real.pi)))
      S (τ₀, (Real.sqrt 2, t₀)) :=
    (htau.contDiffWithinAt (s := Set.univ)).comp (τ₀, (Real.sqrt 2, t₀)) hlag_reflect
      (fun z _ => trivial)
  have heq2 : (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      =ᶠ[𝓝[S] (τ₀, (Real.sqrt 2, t₀))]
      (fun z => Work.RPV.tau Real.pi
        (lagPt D.W D.Γc D.Ac D.rho z.1 (-z.2.1) (z.2.2 - Real.pi))) := by
    have hmem : {z : ℝ × (ℝ × ℝ) | 0 < z.2.1} ∈ 𝓝[S] (τ₀, (Real.sqrt 2, t₀)) :=
      mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds
          (by norm_num : (0 : ℝ) < Real.sqrt 2))
    filter_upwards [hmem, self_mem_nhdsWithin] with z hzpos _
    have hnx : -z.2.1 ≤ 0 := by linarith
    rw [lagPt, if_neg (not_le.mpr hzpos)]
    rw [show lagPt D.W D.Γc D.Ac D.rho z.1 (-z.2.1) (z.2.2 - Real.pi)
        = basePt D.W D.Γc D.Ac D.rho z.1 (-z.2.1) (z.2.2 - Real.pi) from by
      rw [lagPt, if_pos hnx]]
  have hptS2 : (τ₀, (Real.sqrt 2, t₀)) ∈ S := ⟨hτ₀, trivial, trivial⟩
  have hfinal := htaucomp.congr_of_eventuallyEq heq2 (heq2.eq_of_nhdsWithin hptS2)
  simpa [hSdef] using hfinal

end Work.RPB.B5
