import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.stretch_defs
import Submission.Work.Geo.DualStretch.massG_api
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.coord_spec
import Submission.Work.Geo.DualStretch.carrier_spec
import Submission.Work.Geo.DualStretch.join_decomp

/-!
# The stretch fixes the points outside the open cube (`stretch_fix_outside`)

`stretch P hP β p α M` rescales the high part of every point of `P.space` by the taper
`taperM β p P hP α M` and renormalises.  This file proves that points `x ∉ PL.openCube β` are
fixed.

The mathematical content is: if `x ∈ P.space = PL.closedCube β` lies on the boundary of the cube
and is not in the open cube, then some coordinate `i` satisfies `|x i| = β`; the level sets of
positive mass all lie inside the carrier of `x` (a face of `P` contained in the cube), and
`x i = β = |x i|` is the *maximum* (or the minimum, after reflecting) of `y ↦ |y i|` on that face,
so each barycentre `bary τ` has `i`-th coordinate exactly `x i`.  Consequently

* `(AOf x) i = (1 - SOf x) * (x i)` and `(BOf x) i = SOf x * (x i)`;

whence the join segment `segOf x = (uOf x, wOf x)` through `x` is contained in the boundary
`bdryCube β` whenever `SOf x ∉ {0, 1}`, so that the taper is `1` there and the stretch is the
identity.  When `SOf x = 0` (all mass low) or `SOf x = 1` (all mass high) the renormalisation is
trivially the identity because `BOf x = 0` resp. `AOf x = 0`.
-/

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

/-! ### Candidates and barycentres -/

/-- The elements of `cands P hP` are exactly the subsets of faces of `P`. -/
lemma sfo_mem_cands_iff {P : Cx n} {hP : P.faces.Finite} {τ : Finset (E n)} :
    τ ∈ cands P hP ↔ ∃ σ ∈ P.faces, τ ⊆ σ := by
  rw [cands, Finset.mem_biUnion]
  constructor
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mp hσ, Finset.mem_powerset.mp hτ⟩
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mpr hσ, Finset.mem_powerset.mpr hτ⟩

/-- The barycentre of a face of a complex triangulating `closedCube β` lies in that cube. -/
lemma sfo_bary_mem_closedCube {β : ℝ} {P : Cx n} (hsp : P.space = PL.closedCube β)
    {τ : Finset (E n)} (hτ : τ ∈ P.faces) : bary τ ∈ PL.closedCube β :=
  simp_subset_closedCube hsp hτ (bary_mem_simp (Geometry.SimplicialComplex.nonempty_of_mem_faces hτ))

/-- The `i`-th coordinate of the barycentre of a face is at most `β`. -/
lemma sfo_bary_apply_le {β : ℝ} {P : Cx n} (hsp : P.space = PL.closedCube β)
    {τ : Finset (E n)} (hτ : τ ∈ P.faces) (i : Fin n) : (bary τ) i ≤ β :=
  le_trans (le_abs_self _) (sfo_bary_mem_closedCube hsp hτ i)

/-- The `i`-th coordinate of the barycentre of a face is at least `-β`. -/
lemma sfo_neg_le_bary_apply {β : ℝ} {P : Cx n} (hsp : P.space = PL.closedCube β)
    {τ : Finset (E n)} (hτ : τ ∈ P.faces) (i : Fin n) : -β ≤ (bary τ) i := by
  have h := sfo_bary_mem_closedCube hsp hτ i
  linarith [neg_abs_le ((bary τ) i)]

/-! ### The low and high parts as sums over the low resp. high candidates -/

lemma sfo_BOf_eq_filter (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) :
    BOf β p P hP x
      = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ), massG P hP x τ • bary τ := by
  rw [BOf, Finset.sum_filter]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases h : LowFace β p τ <;> simp [h]

lemma sfo_SOf_eq_filter (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) :
    SOf β p P hP x
      = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ), massG P hP x τ := by
  rw [SOf, Finset.sum_filter]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases h : LowFace β p τ <;> simp [h]

lemma sfo_AOf_eq_filter (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) :
    AOf β p P hP x
      = ∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ), massG P hP x τ • bary τ := by
  rw [AOf, Finset.sum_filter]

/-- The total low mass is `1 - SOf`. -/
lemma sfo_low_sum_eq {β : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) :
    ∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ), massG P hP x τ
      = 1 - SOf β p P hP x := by
  have h1 := (massG_api P hP hx).2.1
  have hsplit := Finset.sum_filter_add_sum_filter_not (cands P hP) (fun τ => LowFace β p τ)
    (fun τ => massG P hP x τ)
  rw [h1] at hsplit
  have hhigh := (sfo_SOf_eq_filter β p P hP x).symm
  linarith

/-! ### The key coordinate identity -/

/-- If `x` lies on the boundary of the cube, then every level set of positive mass has its
barycentre on the same coordinate hyperplane `|y i| = β` as `x`. -/
lemma sfo_massG_mul_bary_apply {β : ℝ} {P : Cx n} (hsp : P.space = PL.closedCube β)
    {hP : P.faces.Finite} {x : E n} (hx : x ∈ P.space) {i : Fin n} (hi : |x i| = β) :
    ∀ τ ∈ cands P hP, massG P hP x τ * (bary τ) i = massG P hP x τ * (x i) := by
  obtain ⟨hnn, hsum1, hcomb, hsubc, hchain, hfaces⟩ := massG_api P hP hx
  have hub : ∀ τ ∈ cands P hP, massG P hP x τ ≠ 0 → (bary τ) i ≤ β := by
    intro τ hτ hm
    have hpos : 0 < massG P hP x τ := lt_of_le_of_ne (hnn τ hτ) (Ne.symm hm)
    exact sfo_bary_apply_le hsp (hfaces τ hpos) i
  have hlb : ∀ τ ∈ cands P hP, massG P hP x τ ≠ 0 → -β ≤ (bary τ) i := by
    intro τ hτ hm
    have hpos : 0 < massG P hP x τ := lt_of_le_of_ne (hnn τ hτ) (Ne.symm hm)
    exact sfo_neg_le_bary_apply hsp (hfaces τ hpos) i
  have h1 : ∑ τ ∈ cands P hP, massG P hP x τ * (bary τ) i = x i := by
    rw [← congrArg (fun y : E n => y i) hcomb]
    simp
  have h2 : ∑ τ ∈ cands P hP, massG P hP x τ * (x i) = x i := by
    rw [← Finset.sum_mul, hsum1, one_mul]
  have hzero : ∑ τ ∈ cands P hP, massG P hP x τ * ((bary τ) i - x i) = 0 := by
    rw [Finset.sum_congr rfl (fun τ (_ : τ ∈ cands P hP) => by rw [mul_sub]),
      Finset.sum_sub_distrib, h1, h2, sub_self]
  intro τ hτ
  by_cases hc : x i ≤ 0
  · have hxc : x i = -β := by
      have : |x i| = -x i := abs_of_nonpos hc
      linarith [hi, this]
    have hnn' : ∀ σ ∈ cands P hP, 0 ≤ massG P hP x σ * ((bary σ) i - x i) := by
      intro σ hσ
      by_cases hm : massG P hP x σ = 0
      · rw [hm, zero_mul]
      · have hle := hlb σ hσ hm
        have h2' : 0 ≤ (bary σ) i - x i := by linarith [hle, hxc]
        exact mul_nonneg (hnn σ hσ) h2'
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn').mp hzero
    have hτ0 := hall τ hτ
    nlinarith [hτ0]
  · have hxc : x i = β := by
      have : |x i| = x i := abs_of_nonneg (le_of_lt (not_le.mp hc))
      linarith [hi, this]
    have hnn' : ∀ σ ∈ cands P hP, massG P hP x σ * ((bary σ) i - x i) ≤ 0 := by
      intro σ hσ
      by_cases hm : massG P hP x σ = 0
      · rw [hm, zero_mul]
      · have hle := hub σ hσ hm
        have h2' : (bary σ) i - x i ≤ 0 := by linarith [hle, hxc]
        exact mul_nonpos_of_nonneg_of_nonpos (hnn σ hσ) h2'
    have hall := (Finset.sum_eq_zero_iff_of_nonpos hnn').mp hzero
    have hτ0 := hall τ hτ
    nlinarith [hτ0]

/-! ### Coordinates of `AOf`, `BOf`, `uOf`, `wOf` on the boundary -/

lemma sfo_AOf_apply_eq {β : ℝ} {p : ℕ} {P : Cx n} (hsp : P.space = PL.closedCube β)
    {hP : P.faces.Finite} {x : E n} (hx : x ∈ P.space) {i : Fin n} (hi : |x i| = β) :
    (AOf β p P hP x) i = (1 - SOf β p P hP x) * (x i) := by
  have hkey := sfo_massG_mul_bary_apply (hP := hP) hsp hx hi
  rw [sfo_AOf_eq_filter]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun τ hτ => hkey τ (Finset.mem_of_mem_filter τ hτ)),
    ← Finset.sum_mul, sfo_low_sum_eq P hP hx]

lemma sfo_BOf_apply_eq {β : ℝ} {p : ℕ} {P : Cx n} (hsp : P.space = PL.closedCube β)
    {hP : P.faces.Finite} {x : E n} (hx : x ∈ P.space) {i : Fin n} (hi : |x i| = β) :
    (BOf β p P hP x) i = SOf β p P hP x * (x i) := by
  have hkey := sfo_massG_mul_bary_apply (hP := hP) hsp hx hi
  rw [sfo_BOf_eq_filter]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun τ hτ => hkey τ (Finset.mem_of_mem_filter τ hτ)),
    ← Finset.sum_mul, sfo_SOf_eq_filter]

lemma sfo_uOf_apply {β : ℝ} {p : ℕ} {P : Cx n} (hsp : P.space = PL.closedCube β)
    {hP : P.faces.Finite} {x : E n} (hx : x ∈ P.space) {i : Fin n} (hi : |x i| = β)
    (hS : SOf β p P hP x ≠ 1) : (uOf β p P hP x) i = x i := by
  have hne : (1 : ℝ) - SOf β p P hP x ≠ 0 := by
    rw [sub_ne_zero]; exact Ne.symm hS
  rw [uOf, ite_eq_right hne, PiLp.smul_apply, smul_eq_mul, sfo_AOf_apply_eq hsp hx hi,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

lemma sfo_wOf_apply {β : ℝ} {p : ℕ} {P : Cx n} (hsp : P.space = PL.closedCube β)
    {hP : P.faces.Finite} {x : E n} (hx : x ∈ P.space) {i : Fin n} (hi : |x i| = β)
    (hS : SOf β p P hP x ≠ 0) : (wOf β p P hP x) i = x i := by
  rw [wOf, ite_eq_right hS, PiLp.smul_apply, smul_eq_mul, sfo_BOf_apply_eq hsp hx hi,
    ← mul_assoc, inv_mul_cancel₀ hS, one_mul]

/-- On the boundary of the cube, and away from the degenerate values `SOf ∈ {0, 1}`, the join
segment through `x` lies in the boundary of the cube. -/
lemma sfo_segOf_mem_BdrySeg {β : ℝ} {p : ℕ} {P : Cx n} (hsp : P.space = PL.closedCube β)
    {hP : P.faces.Finite} {x : E n} (hx : x ∈ P.space) {i : Fin n} (hi : |x i| = β)
    (hS0 : SOf β p P hP x ≠ 0) (hS1 : SOf β p P hP x ≠ 1) :
    segOf β p P hP x ∈ BdrySeg β := by
  have hu : (uOf β p P hP x) i = x i := sfo_uOf_apply hsp hx hi hS1
  have hw : (wOf β p P hP x) i = x i := sfo_wOf_apply hsp hx hi hS0
  intro t ht
  refine ⟨i, ?_⟩
  show |((1 - t) • uOf β p P hP x + t • wOf β p P hP x) i| = β
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, hu, hw,
    show (1 - t) * (x i) + t * (x i) = x i by ring, hi]

/-- The taper is `1` on segments lying in the boundary of the cube. -/
lemma sfo_taperM_eq_one_of_segOf_mem {β α M : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite)
    {x : E n} (h : segOf β p P hP x ∈ BdrySeg β) : taperM β p P hP α M x = 1 := by
  rw [taperM, Metric.infDist_zero_of_mem h, zero_div]
  norm_num [clamp01]

/-! ### The degenerate cases `SOf = 0` and `SOf = 1` -/

lemma sfo_BOf_eq_zero_of_SOf_eq_zero {β : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hS : SOf β p P hP x = 0) : BOf β p P hP x = 0 := by
  rw [sfo_BOf_eq_filter]
  refine Finset.sum_eq_zero (fun τ hτ => ?_)
  have h2 : ∑ σ ∈ (cands P hP).filter (fun σ => ¬ LowFace β p σ), massG P hP x σ = 0 := by
    rw [← sfo_SOf_eq_filter]; exact hS
  have hnn : ∀ σ ∈ (cands P hP).filter (fun σ => ¬ LowFace β p σ), 0 ≤ massG P hP x σ :=
    fun σ _ => le_max_left (0 : ℝ) _
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h2 τ hτ
  rw [this, zero_smul]

lemma sfo_AOf_eq_zero_of_SOf_eq_one {β : ℝ} {p : ℕ} (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) (hS : SOf β p P hP x = 1) : AOf β p P hP x = 0 := by
  rw [sfo_AOf_eq_filter]
  refine Finset.sum_eq_zero (fun τ hτ => ?_)
  have h2 : ∑ σ ∈ (cands P hP).filter (fun σ => LowFace β p σ), massG P hP x σ = 0 := by
    rw [sfo_low_sum_eq P hP hx, hS]; ring
  have hnn : ∀ σ ∈ (cands P hP).filter (fun σ => LowFace β p σ), 0 ≤ massG P hP x σ :=
    fun σ _ => le_max_left (0 : ℝ) _
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h2 τ hτ
  rw [this, zero_smul]

/-! ### The taper is `1` off the open cube -/

/-- A point of `P.space = closedCube β` outside the open cube lies on the boundary
`bdryCube β`. -/
lemma sfo_mem_bdryCube {β : ℝ} {P : Cx n} (hsp : P.space = PL.closedCube β) {x : E n}
    (hx : x ∈ P.space) (hx' : x ∉ PL.openCube β) : x ∈ bdryCube β := by
  have hxcl : x ∈ PL.closedCube β := hsp ▸ hx
  have hex : ∃ i : Fin n, β ≤ |x i| := by
    have h : ¬ ∀ i : Fin n, |x i| < β := hx'
    push Not at h
    exact h
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, le_antisymm (hxcl i) hi⟩

/-! ### The target -/

theorem stretch_fix_outside {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    {β α M : ℝ} {p : ℕ} (hM : 1 ≤ M) (hsp : P.space = PL.closedCube β) {x : PL.E n}
    (hx : x ∉ PL.openCube β) :
    Work.Geo.DualStretch.stretch P hP β p α M x = x := by
  rcases eq_or_ne n 0 with hn0 | hn0
  · subst hn0
    exact absurd (fun (i : Fin 0) => Fin.elim0 i) hx
  by_cases hxs : x ∈ P.space
  · have hxcl : x ∈ PL.closedCube β := hsp ▸ hxs
    obtain ⟨i, hi⟩ : ∃ i : Fin n, |x i| = β := by
      obtain ⟨i, hi⟩ := sfo_mem_bdryCube hsp hxs hx
      exact ⟨i, hi⟩
    have hSnn : 0 ≤ SOf β p P hP x := by
      rw [SOf]
      refine Finset.sum_nonneg fun τ _ => ?_
      by_cases h : LowFace β p τ
      · simp [h]
      · simp only [h, ite_false]; exact le_max_left (0 : ℝ) _
    have hSle : SOf β p P hP x ≤ 1 := by
      rw [SOf]
      calc ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ)
          ≤ ∑ τ ∈ cands P hP, massG P hP x τ :=
            Finset.sum_le_sum fun τ hτ => by
              by_cases h : LowFace β p τ
              · simp only [h, ite_true]; exact le_max_left (0 : ℝ) _
              · simp [h]
        _ = 1 := (massG_api P hP hxs).2.1
    by_cases hS0 : SOf β p P hP x = 0
    · rw [stretch_unfold P hP hxs]
      have hB : BOf β p P hP x = 0 := sfo_BOf_eq_zero_of_SOf_eq_zero P hP hS0
      have hA : AOf β p P hP x = x := by
        have h := AOf_add_BOf (β := β) (p := p) P hP hxs
        rw [hB, add_zero] at h
        exact h
      have hden : denOf β p P hP α M x = 1 := by rw [denOf, hS0]; ring
      rw [hden, hA, hB, smul_zero, add_zero, inv_one, one_smul]
    · by_cases hS1 : SOf β p P hP x = 1
      · rw [stretch_unfold P hP hxs]
        have hA : AOf β p P hP x = 0 := sfo_AOf_eq_zero_of_SOf_eq_one P hP hxs hS1
        have hBx : BOf β p P hP x = x := by
          have h := AOf_add_BOf (β := β) (p := p) P hP hxs
          rw [hA, zero_add] at h
          exact h
        have hden : denOf β p P hP α M x = taperM β p P hP α M x := by rw [denOf, hS1]; ring
        have htpos : 0 < taperM β p P hP α M x := taperM_pos (by linarith) p P hP x
        rw [hden, hA, zero_add, smul_smul, inv_mul_cancel₀ (ne_of_gt htpos), one_smul]
        exact hBx
      · have hseg : segOf β p P hP x ∈ BdrySeg β := sfo_segOf_mem_BdrySeg hsp hxs hi hS0 hS1
        have ht : taperM β p P hP α M x = 1 := sfo_taperM_eq_one_of_segOf_mem P hP hseg
        rw [stretch_unfold P hP hxs, ht]
        have hden : denOf β p P hP α M x = 1 := by rw [denOf, ht]; ring
        simp only [hden, inv_one, one_smul, AOf_add_BOf (β := β) (p := p) P hP hxs]
  · rw [stretch, stretchM, ite_eq_right hxs]

end Work.Geo.DualStretch
