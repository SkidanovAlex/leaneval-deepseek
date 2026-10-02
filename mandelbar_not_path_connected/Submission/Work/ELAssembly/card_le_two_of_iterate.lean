import Mathlib
import Submission.Work.ELPull.Defs
import Submission.Work.ELPull.landsN_image
import Submission.Work.SeedDyn.PortraitCount.eq_add_half_of_T_eq
import Submission.Work.SeedDyn.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `ELAssembly` — the "at most two rays" lemma along a backward orbit (`L1`)

If exactly two external rays (of angles `u ≠ v` in `[0,1)`) land at a point `y` of the
dynamical plane of the tricorn `T_c` (`LandsN`), then at every iterated preimage of `y` under
`T_c` at most two rays of angles in `[0,1)` land.  This is the elementary orbit-portrait
count: the ray at angle `θ` landing at `z` is carried by `T_c` to the ray at angle `T θ` landing
at `T_c z`, so the landing angles of `z` map into those of `T_c z`; and the orbit-portrait input
`Work.ELPull.PortraitCount` provides that this map is injective at every preimage of a two-ray
point.

## The two ingredients

* **The image rule** (`clt_landsN_image`): from the Böttcher functional equation for the
  coordinate `dynPhi c` — here supplied directly by the hypothesis
  `hB : IsDynBottcher c (dynPhi c)`, which is exactly `hB.2.1` — the ray of angle `θ` landing at
  `z` maps to the ray of angle `T θ = -2θ mod 1` landing at `T_c z`.  This is
  `Work.ELPull.landsN_image` with `hφ` replaced by `hB` (`rayPt_Tantibar` for `dynPhi`).

* **The fiber of `T`** (`clt_T_fiber`): a point of `[0,1)` has at most two `T`-preimages in
  `[0,1)`, given explicitly by `⌊-u/2⌋`-style fractional parts; this is
  `Work.SeedDyn.PortraitCount.eq_add_half_of_T_eq` unwound to the two candidate angles
  `Int.fract (-u/2)`, `Int.fract (-u/2 + 1/2)`.

The one-step descent `clt_step_le_two` then splits on whether the landing-angle set of the
image point `w = T_c z` is a subsingleton (then every landing angle of `z` lies in the explicit
two-element fiber of a single angle of `w`) or has two distinct elements (then
`PortraitCount` makes `T` injective on the landing angles of `z`).  The main lemma is the
induction on `k`.
-/

namespace Work.ELAssembly

open Classical Set Function Filter
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## 1. The angle map `T` and its two-point fibers -/

/-- `T θ = -2θ mod 1` always lies in `Ico 0 1`. -/
private theorem clt_T_mem_Ico (θ : ℝ) : Work.ELPull.T θ ∈ Set.Ico 0 1 := by
  rw [Work.ELPull.T_def]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **The fiber of `T` over a point of `[0,1)`.**  Every `θ ∈ Ico 0 1` with `T θ = u` is one of
the two explicit preimages `Int.fract (-u/2)`, `Int.fract (-u/2 + 1/2)` (both in `Ico 0 1`).

The first preimage is `T`-mapped to `u` by the periodicity of `Int.fract`; the dichotomy is
`Work.SeedDyn.PortraitCount.eq_add_half_of_T_eq`. -/
private theorem clt_T_fiber {u θ : ℝ} (hu : u ∈ Set.Ico 0 1) (hθ : θ ∈ Set.Ico 0 1)
    (h : Work.ELPull.T θ = u) :
    θ = Int.fract (-u / 2) ∨ θ = Int.fract (-u / 2 + 1 / 2) := by
  set P := Int.fract (-u / 2) with hP
  set Q := Int.fract (-u / 2 + 1 / 2) with hQ
  have hPIco : P ∈ Set.Ico 0 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rcases eq_or_ne θ P with hEq | hne
  · exact Or.inl hEq
  · have hTP : Work.ELPull.T P = u := by
      rw [hP, Work.ELPull.T_def]
      have h1 : -u / 2 = Int.fract (-u / 2) + ((⌊-u / 2⌋ : ℤ) : ℝ) :=
        (Int.fract_add_floor (-u / 2)).symm
      have h2 : -2 * Int.fract (-u / 2) = u + ((2 * ⌊-u / 2⌋ : ℤ) : ℝ) := by
        have := h1; push_cast at this ⊢; linarith
      rw [h2, Int.fract_add_intCast, Int.fract_eq_self.mpr hu]
    have hhalf := Work.SeedDyn.PortraitCount.eq_add_half_of_T_eq hθ hPIco
      (h.trans hTP.symm) hne
    have hkey : Int.fract (-u / 2) + 1 / 2
        = (-u / 2 + 1 / 2) + ((-⌊-u / 2⌋ : ℤ) : ℝ) := by
      have hh := Int.self_sub_fract (-u / 2)
      push_cast
      linarith
    have hQeq : Q = Int.fract (P + 1 / 2) := by
      calc Q = Int.fract (-u / 2 + 1 / 2) := hQ
        _ = Int.fract ((-u / 2 + 1 / 2) + ((-⌊-u / 2⌋ : ℤ) : ℝ)) := by
              rw [Int.fract_add_intCast]
        _ = Int.fract (Int.fract (-u / 2) + 1 / 2) := by rw [hkey]
        _ = Int.fract (P + 1 / 2) := by rw [hP]
    rcases hhalf with hcase | hcase
    · have hPm : P - 1 / 2 ∈ Set.Ico 0 1 := by
        constructor <;> linarith [hθ.1, hθ.2]
      right
      rw [hQeq, show P + 1 / 2 = (P - 1 / 2) + ((1 : ℤ) : ℝ) by push_cast; ring,
        Int.fract_add_intCast, Int.fract_eq_self.mpr hPm]
      linarith
    · have hPp : P + 1 / 2 ∈ Set.Ico 0 1 := by
        constructor <;> linarith [hθ.1, hθ.2, hPIco.1]
      right
      rw [hQeq, Int.fract_eq_self.mpr hPp]
      linarith

/-! ## 2. The image rule for landing rays, from `hB : IsDynBottcher c (dynPhi c)` -/

/-- **The Böttcher functional equation for `dynPhi c`**, read off directly from the hypothesis
`IsDynBottcher c (dynPhi c)` (the second component is the functional equation on the escaping
set, which is the complement of the filled Julia set). -/
private theorem clt_dynPhi_Tantibar {c : ℂ}
    (hB : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhi c))
    {z : ℂ} (hz : z ∉ Work.ParamRays.filledJulia c) :
    Work.ParamRays.dynPhi c (Tantibar c z) = (starRingEnd ℂ) (Work.ParamRays.dynPhi c z) ^ 2 := by
  have hesc : Work.ParamRays.Escaping c z :=
    (Work.ParamRays.escaping_iff_not_bounded c z).mpr
      (by simpa [Work.ParamRays.filledJulia] using hz)
  exact hB.2.1 z hesc

/-- **The image of a ray point** (the `hB`-version of `Work.ELPull.rayPt_Tantibar`).  For
`t > 1`, `T_c` carries the point of the ray of angle `θ` at level `t` to the point of the ray of
angle `T θ` at level `t ^ 2`. -/
private theorem clt_rayPt_Tantibar {c : ℂ} (hN : Work.ELPull.DynB c)
    (hB : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhi c))
    {θ t : ℝ} (ht : 1 < t) :
    hN.rayPt (Work.ELPull.T θ) (t ^ 2) = Tantibar c (hN.rayPt θ t) := by
  have hzt : 1 < t ^ 2 := by nlinarith
  have hzF : hN.rayPt θ t ∉ Work.ParamRays.filledJulia c := hN.rayPt_notMem ht
  have hTF : Tantibar c (hN.rayPt θ t) ∉ Work.ParamRays.filledJulia c := by
    have hesc : Work.ParamRays.Escaping c (hN.rayPt θ t) :=
      (Work.ParamRays.escaping_iff_not_bounded c _).mpr
        (by simpa [Work.ParamRays.filledJulia] using hzF)
    have hT := hesc.iterate 1
    simp only [Work.ParamRays.filledJulia, Set.mem_ofPred_eq]
    refine (Work.ParamRays.escaping_iff_not_bounded c (Tantibar c (hN.rayPt θ t))).mp ?_
    simpa [Work.ParamRays.orbit] using hT
  have hz2F : hN.rayPt (Work.ELPull.T θ) (t ^ 2) ∉ Work.ParamRays.filledJulia c :=
    hN.rayPt_notMem hzt
  have hEq : Work.ParamRays.dynPhi c (Tantibar c (hN.rayPt θ t))
      = Work.ParamRays.dynPhi c (hN.rayPt (Work.ELPull.T θ) (t ^ 2)) := by
    rw [clt_dynPhi_Tantibar hB hzF, hN.Phi_rayPt ht, Work.ELPull.rayPoint_T_conj_sq]
    exact (hN.Phi_rayPt hzt).symm
  exact (hN.injOn_Phi hTF hz2F hEq).symm

/-- **The image of a landing ray** (the `hB`-version of `Work.ELPull.landsN_image`).  If the ray
of angle `θ` lands at `y`, then the ray of angle `T θ` lands at `T_c y`. -/
private theorem clt_landsN_image {c : ℂ} (hN : Work.ELPull.DynB c)
    (hB : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhi c))
    {θ : ℝ} {y : ℂ} (h : Work.ELPull.LandsN hN θ y) :
    Work.ELPull.LandsN hN (Work.ELPull.T θ) (Tantibar c y) := by
  have hmem : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Ioi 1), 1 < t := self_mem_nhdsWithin
  have hcont : Continuous (Tantibar c) := by
    change Continuous (fun z : ℂ => (starRingEnd ℂ z) ^ 2 + c)
    exact (Complex.continuous_conj.pow 2).add_const c
  have h1 : Tendsto (fun t : ℝ => Tantibar c (hN.rayPt θ t))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Tantibar c y)) :=
    (hcont.tendsto y).comp h
  have hfg : (fun t : ℝ => Tantibar c (hN.rayPt θ t))
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
        (fun t : ℝ => hN.rayPt (Work.ELPull.T θ) (t ^ 2)) := by
    filter_upwards [hmem] with t ht
    exact (clt_rayPt_Tantibar hN hB ht).symm
  have h2 : Tendsto (fun t : ℝ => hN.rayPt (Work.ELPull.T θ) (t ^ 2))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Tantibar c y)) := h1.congr' hfg
  have hsqrt : Tendsto (fun s : ℝ => Real.sqrt s) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa [Real.sqrt_one] using
        (Real.continuous_sqrt.continuousAt (x := (1:ℝ))).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)).mpr (by simpa using hs)
  have h3 : Tendsto (fun s : ℝ => hN.rayPt (Work.ELPull.T θ) ((Real.sqrt s) ^ 2))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Tantibar c y)) := h2.comp hsqrt
  have h4 : Tendsto (fun s : ℝ => hN.rayPt (Work.ELPull.T θ) s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Tantibar c y)) := by
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Real.sq_sqrt (lt_trans zero_lt_one hs).le]
  exact h4

/-! ## 3. The one-step descent -/

/-- **One step of the descent.**  If the point `w = T_c z` has at most two landing rays (with
angles in `Ico 0 1`), then so has `z`.

* If the landing-angle set `Sw` of `w` is a *subsingleton* and nonempty, every landing angle of
  `z` is `T`-mapped to its unique element `u₁`, hence lies in the explicit fiber
  `{Int.fract (-u₁/2), Int.fract (-u₁/2 + 1/2)}` (`clt_T_fiber`).  If `Sw` is empty, there is
  nothing to prove.
* If `Sw` contains two distinct angles `a ≠ b`, then (since `Sw ⊆ {u₀, v₀}`) the two-ray
  hypothesis of `PortraitCount` holds at `w`, so `T` is injective on the landing angles of `z`;
  and `T` carries those into `Sw ⊆ {a, b}`, so `z` has at most one landing angle above each
  of `a`, `b`. -/
private theorem clt_step_le_two {c : ℂ} {hN : Work.ELPull.DynB c}
    (himg : ∀ {θ' : ℝ} {y : ℂ}, Work.ELPull.LandsN hN θ' y →
      Work.ELPull.LandsN hN (Work.ELPull.T θ') (Tantibar c y))
    (hcount : Work.ELPull.PortraitCount hN)
    {w z : ℂ} (hzw : Tantibar c z = w)
    (hw : ∃ u v : ℝ, u ∈ Set.Ico 0 1 ∧ v ∈ Set.Ico 0 1 ∧
      ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → Work.ELPull.LandsN hN θ w → θ = u ∨ θ = v) :
    ∃ u' v' : ℝ, u' ∈ Set.Ico 0 1 ∧ v' ∈ Set.Ico 0 1 ∧
      ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → Work.ELPull.LandsN hN θ z → θ = u' ∨ θ = v' := by
  obtain ⟨u₀, v₀, hu₀, hv₀, hw⟩ := hw
  set Sw : Set ℝ := {θ : ℝ | θ ∈ Set.Ico 0 1 ∧ Work.ELPull.LandsN hN θ w} with hSw
  have himgT : ∀ {θ : ℝ}, θ ∈ Set.Ico 0 1 → Work.ELPull.LandsN hN θ z →
      Work.ELPull.LandsN hN (Work.ELPull.T θ) w := by
    intro θ _ hland
    have h := himg hland
    rwa [hzw] at h
  by_cases hss : Sw.Subsingleton
  · by_cases hne : Sw.Nonempty
    · obtain ⟨u₁, hu₁⟩ := hne
      refine ⟨Int.fract (-u₁ / 2), Int.fract (-u₁ / 2 + 1 / 2), ?_, ?_, ?_⟩
      · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      · intro θ hθ hland
        exact clt_T_fiber hu₁.1 hθ (hss ⟨clt_T_mem_Ico θ, himgT hθ hland⟩ hu₁)
    · refine ⟨0, 0, ⟨le_refl 0, by norm_num⟩, ⟨le_refl 0, by norm_num⟩, ?_⟩
      intro θ hθ hland
      exact absurd ⟨Work.ELPull.T θ, clt_T_mem_Ico θ, himgT hθ hland⟩ hne
  · push_neg at hss
    obtain ⟨a, haSw, b, hbSw, hab⟩ := hss
    have haIco : a ∈ Set.Ico 0 1 := haSw.1
    have hla : Work.ELPull.LandsN hN a w := haSw.2
    have hbIco : b ∈ Set.Ico 0 1 := hbSw.1
    have hlb : Work.ELPull.LandsN hN b w := hbSw.2
    have hauv : a = u₀ ∨ a = v₀ := hw a haIco hla
    have hbuv : b = u₀ ∨ b = v₀ := hw b hbIco hlb
    -- `{u₀, v₀} = {a, b}`: the two distinct landing angles of `w` exhaust the bound
    have hpq : ({u₀, v₀} : Set ℝ) ⊆ ({a, b} : Set ℝ) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · rcases hauv with h | h <;> rcases hbuv with h' | h'
        · exact absurd (h.trans h'.symm) hab
        · exact Or.inl h.symm
        · exact Or.inr h'.symm
        · exact absurd (h.trans h'.symm) hab
      · rcases hauv with h | h <;> rcases hbuv with h' | h'
        · exact absurd (h.trans h'.symm) hab
        · exact Or.inr h'.symm
        · exact Or.inl h.symm
        · exact absurd (h.trans h'.symm) hab
    have hset : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → Work.ELPull.LandsN hN θ w → θ = a ∨ θ = b :=
      fun θ hθ hland => hpq (hw θ hθ hland)
    have hport : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
        (Work.ELPull.LandsN hN θ w ↔ θ = a ∨ θ = b) := by
      intro θ hθ
      refine ⟨hset θ hθ, ?_⟩
      rintro (rfl | rfl)
      · exact hla
      · exact hlb
    have hinj := hcount w z hzw ⟨a, b, haIco, hbIco, hab, hport⟩
    -- one chosen landing angle of `z` above `a`, and one above `b`
    refine ⟨(if h : ∃ θ : ℝ, θ ∈ Set.Ico 0 1 ∧ Work.ELPull.LandsN hN θ z
                ∧ Work.ELPull.T θ = a then Classical.choose h else 0),
            (if h : ∃ θ : ℝ, θ ∈ Set.Ico 0 1 ∧ Work.ELPull.LandsN hN θ z
                ∧ Work.ELPull.T θ = b then Classical.choose h else 0), ?_, ?_, ?_⟩
    · by_cases h : ∃ θ : ℝ, θ ∈ Set.Ico 0 1 ∧ Work.ELPull.LandsN hN θ z
          ∧ Work.ELPull.T θ = a
      · rw [dif_pos h]; exact (Classical.choose_spec h).1
      · rw [dif_neg h]; exact ⟨le_refl 0, by norm_num⟩
    · by_cases h : ∃ θ : ℝ, θ ∈ Set.Ico 0 1 ∧ Work.ELPull.LandsN hN θ z
          ∧ Work.ELPull.T θ = b
      · rw [dif_pos h]; exact (Classical.choose_spec h).1
      · rw [dif_neg h]; exact ⟨le_refl 0, by norm_num⟩
    · intro θ hθ hland
      rcases hset (Work.ELPull.T θ) (clt_T_mem_Ico θ) (himgT hθ hland) with hT | hT
      · left
        have hex : ∃ θ : ℝ, θ ∈ Set.Ico 0 1 ∧ Work.ELPull.LandsN hN θ z
            ∧ Work.ELPull.T θ = a := ⟨θ, hθ, hland, hT⟩
        rw [dif_pos hex]
        have hspec := Classical.choose_spec hex
        refine (hinj _ θ hspec.1 hθ hspec.2.1 hland ?_).symm
        rw [hspec.2.2, hT]
      · right
        have hex : ∃ θ : ℝ, θ ∈ Set.Ico 0 1 ∧ Work.ELPull.LandsN hN θ z
            ∧ Work.ELPull.T θ = b := ⟨θ, hθ, hland, hT⟩
        rw [dif_pos hex]
        have hspec := Classical.choose_spec hex
        refine (hinj _ θ hspec.1 hθ hspec.2.1 hland ?_).symm
        rw [hspec.2.2, hT]

/-! ## 4. The iterated statement -/

theorem card_le_two_of_iterate {c : ℂ} (hN : Work.ELPull.DynB c)
    (hB : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhi c))
    (hP : Work.ELPull.PortraitCount hN)
    {y z : ℂ} {u v : ℝ} (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1) (huv : u ≠ v)
    (hy : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.ELPull.LandsN hN θ y ↔ θ = u ∨ θ = v))
    (k : ℕ) (hTz : ((LeanEval.ComplexAnalysis.Tantibar c)^[k]) z = y) :
    ∃ u' v' : ℝ, u' ∈ Set.Ico 0 1 ∧ v' ∈ Set.Ico 0 1 ∧
      ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → Work.ELPull.LandsN hN θ z → θ = u' ∨ θ = v' := by
  have himg : ∀ {θ' : ℝ} {y : ℂ}, Work.ELPull.LandsN hN θ' y →
      Work.ELPull.LandsN hN (Work.ELPull.T θ') (Tantibar c y) :=
    fun h => clt_landsN_image hN hB h
  have hy' : ∃ u' v' : ℝ, u' ∈ Set.Ico 0 1 ∧ v' ∈ Set.Ico 0 1 ∧
      ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → Work.ELPull.LandsN hN θ y → θ = u' ∨ θ = v' :=
    ⟨u, v, hu, hv, fun θ hθ hl => (hy θ hθ).mp hl⟩
  have P : ∀ k z, ((Tantibar c)^[k]) z = y →
      ∃ u' v' : ℝ, u' ∈ Set.Ico 0 1 ∧ v' ∈ Set.Ico 0 1 ∧
        ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → Work.ELPull.LandsN hN θ z → θ = u' ∨ θ = v' := by
    intro k
    induction k with
    | zero =>
        intro z hz
        rw [Function.iterate_zero_apply] at hz
        rw [hz]
        exact hy'
    | succ k ih =>
        intro z hz
        have h1 : ((Tantibar c)^[k]) (Tantibar c z) = y := by
          rw [Function.iterate_succ_apply] at hz; exact hz
        exact clt_step_le_two himg hP rfl (ih (Tantibar c z) h1)
  exact P k z hTz

end Work.ELAssembly
