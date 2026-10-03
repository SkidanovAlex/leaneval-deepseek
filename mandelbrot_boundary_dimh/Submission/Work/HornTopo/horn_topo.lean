import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basin
import Submission.Work.Horn.Basin.ends_mem_aux
import Submission.Work.Parab.basinEnters.zero_not_mem_basin

/-!
# AREA HORN-TOPO: the topology of `B̃ = φ₀⁻¹(B)` (Shishikura, Prop. 5.3, opening lines)

For `f₀ ∈ 𝓕₀` with immediate basin `B` and §4.1 data `d : ParabData f₀ D₀`, we prove
`HornTopoStatement`: the two components

`Bu = connectedComponentIn B̃ (i(η₀+1))`,  `Bl = connectedComponentIn B̃ (-i(η₀+1))`,
`B̃ = {w | w ∈ Dφ ∧ φ w ∈ B}`,

are open, `T`-invariant (`w ↦ w + 1`), contain the upper/lower half planes `{±Im > η₀}`, and are
contained in `DE = φ₀⁻¹(basin)`.

## Route

1. `Ω₊ ⊆ B` ("`B` is unique and contains `Ω₊`"): `Ω₊` is preconnected and lies in the basin, and it
   meets `B` because the orbit of the critical point `c ∈ B` stays in `B` (so never hits `0`, which
   is not in the basin) and therefore enters the petal by `basin_enter`; maximality of `B` among
   preconnected subsets of the basin finishes.
2. `ends_mem_aux` (workspace) gives `η > 0` with `φ w ∈ B` for `η < |Im w|`.  Maximality of `B`
   then gives `φ({Im > η₀}) ⊆ B` and `φ({Im < -η₀}) ⊆ B`: each half plane is convex hence
   preconnected, lies in the basin by `ends_sub`, and meets `B` at a point of large `|Im|`.
3. `B̃` is open (`Dφ` open, `φ` continuous on it, `B` open), and components of open subsets of the
   locally connected space `ℂ` are open.
4. `T`-invariance of the components.  Forward: `w ∈ B̃ → w+1 ∈ B̃`, because `φ w ∈ B ⊆ D₀`, so
   `w + 1 ∈ Dφ` by `succ_iff` and `φ (w+1) = f₀ (φ w) ∈ B`; the component is upgraded by
   preconnectedness.  Backward: for `w ∈ X` (`X` one of the components) put `S = {u | u + 1 ∈ X}`;
   `φ '' S` is preconnected, lies in `D₀` (`succ_iff`), is mapped by `f₀` into `B` (`φ_abel`), and
   meets `B` (at the end of `X`); backward invariance of the basin plus maximality give
   `φ '' S ⊆ B`, so `S ⊆ B̃`, and preconnectedness of `S` gives `S ⊆ X`.
-/

namespace Work.HornTopo

open MandelDim
open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} {d : ParabData f₀ D₀}

/-! ## Convexity of the half planes of `ℂ` -/

lemma convex_im_gt (a : ℝ) : Convex ℝ {w : ℂ | a < w.im} := by
  intro x hx y hy p q hp hq hpq
  change a < x.im at hx
  change a < y.im at hy
  change a < (p • x + q • y).im
  have him : (p • x + q • y).im = p * x.im + q * y.im := by
    simp [Complex.add_im]
  rw [him]
  rcases lt_or_eq_of_le hp with hppos | hp0
  · have h1 : p * a ≤ p * x.im := mul_le_mul_of_nonneg_left hx.le hp
    have hstr : p * a < p * x.im := mul_lt_mul_of_pos_left hx hppos
    have h3 : p * a + q * a = a := by rw [← add_mul, hpq, one_mul]
    have h4 : q * a ≤ q * y.im := mul_le_mul_of_nonneg_left hy.le hq
    linarith
  · have hp0' : p = 0 := hp0.symm
    have hq1 : q = 1 := by linarith
    rw [hp0', zero_mul, hq1, one_mul, zero_add]
    exact hy

lemma convex_im_lt (a : ℝ) : Convex ℝ {w : ℂ | w.im < a} := by
  intro x hx y hy p q hp hq hpq
  change x.im < a at hx
  change y.im < a at hy
  change (p • x + q • y).im < a
  have him : (p • x + q • y).im = p * x.im + q * y.im := by
    simp [Complex.add_im]
  rw [him]
  rcases lt_or_eq_of_le hp with hppos | hp0
  · have h1 : p * x.im ≤ p * a := mul_le_mul_of_nonneg_left hx.le hp
    have hstr : p * x.im < p * a := mul_lt_mul_of_pos_left hx hppos
    have h3 : p * a + q * a = a := by rw [← add_mul, hpq, one_mul]
    have h4 : q * y.im ≤ q * a := mul_le_mul_of_nonneg_left hy.le hq
    linarith
  · have hp0' : p = 0 := hp0.symm
    have hq1 : q = 1 := by linarith
    rw [hp0', zero_mul, hq1, one_mul, zero_add]
    exact hy

/-! ## Basic facts about the immediate basin -/

/-- The immediate basin is contained in the domain of definition of `f₀` (a basin point has a
neighbourhood on which the zeroth iterate `id` stays inside `D₀`). -/
lemma subset_D₀_of_immediateBasin {f : ℂ → ℂ} {D B : Set ℂ} (hB : IsImmediateBasin f D B) :
    B ⊆ D := by
  intro z hz
  obtain ⟨U, hU, hiter, _⟩ := hB.2.2.1 hz
  exact hiter 0 (mem_of_mem_nhds hU)

/-- **Backward invariance of the parabolic basin inside `D`**: if `z ∈ D` and `f z` lies in the
basin then so does `z`.  For a ball `V ∋ z` inside `D` with `f '' V ⊆ U` (the witness of `f z`) we
get `f^[n] '' V ⊆ D` for every `n` and `f^[n] → 0` uniformly on `V`. -/
lemma mem_basin_of_image_mem {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : DifferentiableOn ℂ f D) {z : ℂ} (hzD : z ∈ D)
    (hz : f z ∈ ParabolicBasin f D) : z ∈ ParabolicBasin f D := by
  obtain ⟨U, hU, hiter, hconv⟩ := hz
  have hcont : ContinuousAt f z := hf.continuousOn.continuousAt (hD.mem_nhds hzD)
  refine ⟨f ⁻¹' U ∩ D, Filter.inter_mem (hcont.preimage_mem_nhds hU) (hD.mem_nhds hzD), ?_, ?_⟩
  · intro n y hy
    cases n with
    | zero => exact hy.2
    | succ k => simpa [Function.iterate_succ_apply] using hiter k hy.1
  · rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hconv ε hε)
    refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn y hy => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [Function.iterate_succ_apply]
    exact hN k (by omega) (f y) hy.1

/-- **`Ω₊ ⊆ B`** ("`B` is unique and contains `Ω₊`").  The petal is preconnected and lies in the
basin; the orbit of the critical point `c ∈ B` stays in `B` — hence never meets `0`, which is not
in the basin — so `basin_enter` produces an iterate in the petal, and maximality of `B` among
preconnected subsets of the basin applies. -/
lemma omega_subset_B {f : ℂ → ℂ} {D B : Set ℂ} {c : ℂ} (hF0 : IsF0Setup f D B c)
    (d : ParabData f D) : d.Ωp ⊆ B := by
  obtain ⟨hgerm, hB, hcB, -, huniq⟩ := hF0
  have hzero : (0 : ℂ) ∉ ParabolicBasin f D :=
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin hgerm
  have hBbasin : B ⊆ ParabolicBasin f D := hB.2.2.1
  have hmap : MapsTo f B B := hB.2.2.2.2.1
  have hiter : ∀ n : ℕ, (f^[n]) c ∈ B := by
    intro n
    induction n with
    | zero => simpa using hcB
    | succ k ih => rw [Function.iterate_succ_apply']; exact hmap ih
  have hne : ∀ n : ℕ, (f^[n]) c ≠ 0 := by
    intro n h0
    exact hzero (h0 ▸ hBbasin (hiter n))
  obtain ⟨n, hn⟩ := d.basin_enter c (hBbasin hcB) hne
  exact hB.2.2.2.1 d.Ωp d.Ωp_conn.isPreconnected d.Ωp_sub ⟨(f^[n]) c, hiter n, hn⟩

/-! ## The half planes map into the basin -/

/-- `φ` maps the upper half plane `{Im > η₀}` into the immediate basin: the image is preconnected
(`φ` is continuous on `Dφ ⊇ {Im > η₀}` by `ends_sub`), lies in the basin, and meets `B` because
`φ` sends the point of imaginary part `|max η₀ η| + 1` there into `B` (hypothesis `hη`, from
`ends_mem_aux`); maximality of `B` finishes. -/
lemma phi_mem_B_of_im_gt {f : ℂ → ℂ} {D B : Set ℂ} (d : ParabData f D)
    (hB : IsImmediateBasin f D B)
    {η : ℝ} (hη : ∀ w : ℂ, η < |w.im| → d.φ w ∈ B)
    {w : ℂ} (hw : d.η₀ < w.im) : d.φ w ∈ B := by
  set w₀ : ℂ := I * (((|d.η₀| + |η| + 1 : ℝ)) : ℂ) with hw₀
  have hw₀im : w₀.im = |d.η₀| + |η| + 1 := by
    rw [hw₀]; simp
  have hr : (0 : ℝ) ≤ |d.η₀| + |η| + 1 := by positivity
  have hbaseH : d.η₀ < w₀.im := by
    rw [hw₀im]
    linarith [le_abs_self d.η₀, abs_nonneg η]
  have hbaseη : η < |w₀.im| := by
    rw [hw₀im, abs_of_nonneg hr]
    linarith [le_abs_self η, abs_nonneg d.η₀]
  have hφw₀ : d.φ w₀ ∈ B := hη w₀ hbaseη
  have hHsub : {u : ℂ | d.η₀ < u.im} ⊆ d.Dφ := fun u hu =>
    (d.ends_sub u (lt_of_lt_of_le hu (le_abs_self u.im))).1
  have hpre : IsPreconnected (d.φ '' {u : ℂ | d.η₀ < u.im}) :=
    (convex_im_gt d.η₀).isPreconnected.image _ (d.φ_holo.continuousOn.mono hHsub)
  have hbasin : d.φ '' {u : ℂ | d.η₀ < u.im} ⊆ ParabolicBasin f D := by
    rintro z ⟨u, hu, rfl⟩
    exact (d.ends_sub u (lt_of_lt_of_le hu (le_abs_self u.im))).2
  have hmeet : (B ∩ d.φ '' {u : ℂ | d.η₀ < u.im}).Nonempty :=
    ⟨d.φ w₀, hφw₀, w₀, hbaseH, rfl⟩
  exact hB.2.2.2.1 _ hpre hbasin hmeet ⟨w, hw, rfl⟩

/-- `φ` maps the lower half plane `{Im < -η₀}` into the immediate basin (same proof as
`phi_mem_B_of_im_gt`, using a point of large negative imaginary part). -/
lemma phi_mem_B_of_im_lt {f : ℂ → ℂ} {D B : Set ℂ} (d : ParabData f D)
    (hB : IsImmediateBasin f D B)
    {η : ℝ} (hη : ∀ w : ℂ, η < |w.im| → d.φ w ∈ B)
    {w : ℂ} (hw : w.im < -d.η₀) : d.φ w ∈ B := by
  set w₀ : ℂ := -(I * (((|d.η₀| + |η| + 1 : ℝ)) : ℂ)) with hw₀
  have hw₀im : w₀.im = -(|d.η₀| + |η| + 1) := by
    rw [hw₀]; simp
  have hr : (0 : ℝ) ≤ |d.η₀| + |η| + 1 := by positivity
  have hbaseH : w₀.im < -d.η₀ := by
    rw [hw₀im]
    linarith [le_abs_self d.η₀, abs_nonneg η]
  have hbaseη : η < |w₀.im| := by
    rw [hw₀im, abs_neg, abs_of_nonneg hr]
    linarith [le_abs_self η, abs_nonneg d.η₀]
  have hφw₀ : d.φ w₀ ∈ B := hη w₀ hbaseη
  have hHsub : {u : ℂ | u.im < -d.η₀} ⊆ d.Dφ := fun u hu => by
    have hu' : u.im < -d.η₀ := hu
    exact (d.ends_sub u (lt_of_lt_of_le (by linarith : d.η₀ < -u.im) (neg_le_abs u.im))).1
  have hpre : IsPreconnected (d.φ '' {u : ℂ | u.im < -d.η₀}) :=
    (convex_im_lt (-d.η₀)).isPreconnected.image _ (d.φ_holo.continuousOn.mono hHsub)
  have hbasin : d.φ '' {u : ℂ | u.im < -d.η₀} ⊆ ParabolicBasin f D := by
    rintro z ⟨u, hu, rfl⟩
    have hu' : u.im < -d.η₀ := hu
    exact (d.ends_sub u (lt_of_lt_of_le (by linarith : d.η₀ < -u.im) (neg_le_abs u.im))).2
  have hmeet : (B ∩ d.φ '' {u : ℂ | u.im < -d.η₀}).Nonempty :=
    ⟨d.φ w₀, hφw₀, w₀, hbaseH, rfl⟩
  exact hB.2.2.2.1 _ hpre hbasin hmeet ⟨w, hw, rfl⟩

/-! ## `B̃` and the shift `w ↦ w ± 1` -/

/-- `B̃` is invariant under `w ↦ w + 1`: `φ w ∈ B ⊆ D₀`, so `w + 1 ∈ Dφ` by `succ_iff`, and
`φ (w+1) = f₀ (φ w) ∈ B` because `B` is forward invariant. -/
lemma Btil_add_one {f : ℂ → ℂ} {D B : Set ℂ} (d : ParabData f D) (hB : IsImmediateBasin f D B)
    {w : ℂ} (hw : w ∈ Btil d B) : w + 1 ∈ Btil d B := by
  have hBD : B ⊆ D := subset_D₀_of_immediateBasin hB
  have h1 : w + 1 ∈ d.Dφ := (d.succ_iff w hw.1).mpr (hBD hw.2)
  exact ⟨h1, by rw [d.φ_abel w hw.1 h1]; exact hB.2.2.2.2.1 hw.2⟩

/-- **The shift `w ↦ w - 1` on a component of `B̃`.**  If `X ⊆ B̃` is preconnected and meets the
strip `{|Im| > η₀}`, then `S = {u | u + 1 ∈ X} ⊆ B̃`.

`φ '' S` is preconnected (`S` is the translate of `X` by `-1`), lies in `D₀` (`succ_iff`: both `u`
and `u + 1` are in `Dφ` for `u ∈ S`), is mapped by `f₀` into `B` (`φ_abel`), and is contained in the
basin (`mem_basin_of_image_mem`), while it meets `B`: for a point `x₀ ∈ X` of large `|Im|` the
point `x₀ - 1 ∈ S` has the same imaginary part, so `φ (x₀ - 1) ∈ B` by `ends_mem_aux`.  Maximality
of `B` gives `φ '' S ⊆ B`, i.e. `S ⊆ B̃`. -/
lemma shift_subset_Btil {f : ℂ → ℂ} {D B : Set ℂ} (d : ParabData f D)
    (hB : IsImmediateBasin f D B) (hgerm : IsParabolicGerm f D)
    {η : ℝ} (hη : ∀ w : ℂ, η < |w.im| → d.φ w ∈ B)
    {X : Set ℂ} (hXpre : IsPreconnected X) (hXsub : X ⊆ Btil d B)
    (hx : (X ∩ {w : ℂ | η < |w.im|}).Nonempty) :
    {u : ℂ | u + 1 ∈ X} ⊆ Btil d B := by
  obtain ⟨x₀, hx₀X, hx₀η⟩ := hx
  have hSsub : {u : ℂ | u + 1 ∈ X} ⊆ d.Dφ := fun u hu => by
    have h1 : u + 1 ∈ d.Dφ := (hXsub hu).1
    simpa using d.left_inv (u + 1) h1
  have hSpre : IsPreconnected (d.φ '' {u : ℂ | u + 1 ∈ X}) := by
    have hS2 : {u : ℂ | u + 1 ∈ X} = (fun z : ℂ => z - 1) '' X := by
      ext u
      constructor
      · intro hu
        exact ⟨u + 1, hu, by ring⟩
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
    rw [hS2]
    exact (hXpre.image _ (continuous_sub_right 1).continuousOn).image _
      (d.φ_holo.continuousOn.mono (fun u hu => by
        rw [← hS2] at hu
        exact hSsub hu))
  have hD₀ : ∀ u ∈ {u : ℂ | u + 1 ∈ X}, d.φ u ∈ D := fun u hu =>
    (d.succ_iff u (hSsub hu)).mp (by simpa using (hXsub hu).1)
  have hfb : ∀ u ∈ {u : ℂ | u + 1 ∈ X}, f (d.φ u) ∈ ParabolicBasin f D := fun u hu => by
    have hu1 : u + 1 ∈ d.Dφ := (hXsub hu).1
    rw [← d.φ_abel u (hSsub hu) hu1]
    exact hB.2.2.1 (hXsub hu).2
  have hbasin : d.φ '' {u : ℂ | u + 1 ∈ X} ⊆ ParabolicBasin f D := by
    rintro z ⟨u, hu, rfl⟩
    exact mem_basin_of_image_mem hgerm.1 hgerm.2.2.1 (hD₀ u hu) (hfb u hu)
  have hmeet : (B ∩ d.φ '' {u : ℂ | u + 1 ∈ X}).Nonempty :=
    ⟨d.φ (x₀ - 1), hη (x₀ - 1) (by rw [Complex.sub_im, Complex.one_im, sub_zero]; exact hx₀η),
      x₀ - 1, by simpa using hx₀X, rfl⟩
  intro u hu
  exact ⟨hSsub hu, hB.2.2.2.1 _ hSpre hbasin hmeet ⟨u, hu, rfl⟩⟩

/-! ## The main theorem -/

theorem horn_topo : HornTopoStatement := by
  intro f₀ D₀ B c d hF0
  have hF0' := hF0
  obtain ⟨hgerm, hB, hcB, hcrit, huniq⟩ := hF0'
  have hInF0 : InF0 f₀ D₀ :=
    ⟨hgerm, B, hB, c, ⟨hcB, hcrit⟩, fun y hy => huniq y hy.1 hy.2⟩
  have hBbasin : B ⊆ ParabolicBasin f₀ D₀ := hB.2.2.1
  -- the petal lies in `B`, and the two ends
  have hOB : d.Ωp ⊆ B := omega_subset_B hF0 d
  obtain ⟨η, _hηpos, hη⟩ := Work.Horn.Basin.ends_mem_aux f₀ D₀ hInF0 d B hB hOB
  have hφHpos : ∀ w : ℂ, d.η₀ < w.im → d.φ w ∈ B := fun w hw => phi_mem_B_of_im_gt d hB hη hw
  have hφHneg : ∀ w : ℂ, w.im < -d.η₀ → d.φ w ∈ B := fun w hw => phi_mem_B_of_im_lt d hB hη hw
  -- openness of `B̃`
  have hBtil_open : IsOpen (Btil d B) := by
    have h : IsOpen (d.Dφ ∩ d.φ ⁻¹' B) := by
      rw [isOpen_iff_mem_nhds]
      intro w hw
      have hcont : ContinuousAt d.φ w :=
        (d.φ_holo.continuousOn).continuousAt (d.Dφ_open.mem_nhds hw.1)
      exact Filter.inter_mem (d.Dφ_open.mem_nhds hw.1)
        (hcont.preimage_mem_nhds (hB.1.mem_nhds hw.2))
    convert h using 1
    ext w
    simp [Btil]
  -- the half planes lie in `B̃`
  have hHpos_sub : {w : ℂ | d.η₀ < w.im} ⊆ Btil d B := fun w hw =>
    ⟨(d.ends_sub w (lt_of_lt_of_le hw (le_abs_self w.im))).1, hφHpos w hw⟩
  have hHneg_sub : {w : ℂ | w.im < -d.η₀} ⊆ Btil d B := fun w hw =>
    ⟨(d.ends_sub w (lt_of_lt_of_le (by
        have hw' : w.im < -d.η₀ := hw
        linarith) (neg_le_abs w.im))).1,
      hφHneg w hw⟩
  -- the base points of the two components, in the exact form of `BuOf`/`BlOf`
  have him_u : (I * ((d.η₀ : ℂ) + 1)).im = d.η₀ + 1 := by simp
  have him_umin : (I * ((d.η₀ : ℂ) + 1) - 1).im = d.η₀ + 1 := by simp
  have him_upl : (I * ((d.η₀ : ℂ) + 1) + 1).im = d.η₀ + 1 := by simp
  have him_l : (-(I * ((d.η₀ : ℂ) + 1))).im = -(d.η₀ + 1) := by simp
  have him_lmin : (-(I * ((d.η₀ : ℂ) + 1)) - 1).im = -(d.η₀ + 1) := by simp
  have him_lpl : (-(I * ((d.η₀ : ℂ) + 1)) + 1).im = -(d.η₀ + 1) := by simp
  have hbase_u : I * ((d.η₀ : ℂ) + 1) ∈ {w : ℂ | d.η₀ < w.im} := by
    rw [Set.mem_ofPred_eq, him_u]; linarith
  have hbase_l : -(I * ((d.η₀ : ℂ) + 1)) ∈ {w : ℂ | w.im < -d.η₀} := by
    rw [Set.mem_ofPred_eq, him_l]; linarith
  -- a point of large imaginary part in each half plane (used as the contact point in the
  -- shift argument below)
  have him_w1 : (I * (((|d.η₀| + |η| + 1 : ℝ)) : ℂ)).im = |d.η₀| + |η| + 1 := by simp
  have hw1_pos : (0 : ℝ) ≤ |d.η₀| + |η| + 1 := by positivity
  have hw1_Hu : d.η₀ < (I * (((|d.η₀| + |η| + 1 : ℝ)) : ℂ)).im := by
    rw [him_w1]; linarith [le_abs_self d.η₀, abs_nonneg η]
  have hw1_Hl : (-(I * (((|d.η₀| + |η| + 1 : ℝ)) : ℂ))).im < -d.η₀ := by
    rw [Complex.neg_im, him_w1]; linarith [le_abs_self d.η₀, abs_nonneg η]
  have hw1_abs : η < |(I * (((|d.η₀| + |η| + 1 : ℝ)) : ℂ)).im| := by
    rw [him_w1, abs_of_nonneg hw1_pos]; linarith [le_abs_self η, abs_nonneg d.η₀]
  have hw1_abs_l : η < |(-(I * (((|d.η₀| + |η| + 1 : ℝ)) : ℂ))).im| := by
    rw [Complex.neg_im, him_w1, abs_neg, abs_of_nonneg hw1_pos]
    linarith [le_abs_self η, abs_nonneg d.η₀]
  -- the half planes lie in the components
  have hHpos_Bu : {w : ℂ | d.η₀ < w.im} ⊆ BuOf d B :=
    (convex_im_gt d.η₀).isPreconnected.subset_connectedComponentIn hbase_u hHpos_sub
  have hHneg_Bl : {w : ℂ | w.im < -d.η₀} ⊆ BlOf d B :=
    (convex_im_lt (-d.η₀)).isPreconnected.subset_connectedComponentIn hbase_l hHneg_sub
  -- openness
  have hBu_open : IsOpen (BuOf d B) := hBtil_open.connectedComponentIn
  have hBl_open : IsOpen (BlOf d B) := hBtil_open.connectedComponentIn
  -- `T`-invariance of `Bu`
  have hBu_add : ∀ w : ℂ, w ∈ BuOf d B → w + 1 ∈ BuOf d B := by
    intro w hw
    have hXsub : BuOf d B ⊆ Btil d B := connectedComponentIn_subset _ _
    have hshift : (fun z : ℂ => z + 1) '' BuOf d B ⊆ Btil d B := by
      rintro u ⟨z, hz, rfl⟩
      exact Btil_add_one d hB (hXsub hz)
    have hpre : IsPreconnected ((fun z : ℂ => z + 1) '' BuOf d B) :=
      isPreconnected_connectedComponentIn.image _ (continuous_add_const 1).continuousOn
    have hunit : I * ((d.η₀ : ℂ) + 1) - 1 ∈ BuOf d B :=
      hHpos_Bu (by rw [Set.mem_ofPred_eq, him_umin]; linarith)
    have hbase : I * ((d.η₀ : ℂ) + 1) ∈ (fun z : ℂ => z + 1) '' BuOf d B :=
      ⟨I * ((d.η₀ : ℂ) + 1) - 1, hunit, by ring⟩
    exact hpre.subset_connectedComponentIn hbase hshift ⟨w, hw, rfl⟩
  have hBu_sub : ∀ w : ℂ, w ∈ BuOf d B → w - 1 ∈ BuOf d B := by
    intro w hw
    have hXsub : BuOf d B ⊆ Btil d B := connectedComponentIn_subset _ _
    have hx : (BuOf d B ∩ {w : ℂ | η < |w.im|}).Nonempty :=
      ⟨I * (((|d.η₀| + |η| + 1 : ℝ)) : ℂ), hHpos_Bu hw1_Hu, hw1_abs⟩
    have hshift : {u : ℂ | u + 1 ∈ BuOf d B} ⊆ Btil d B :=
      shift_subset_Btil d hB hgerm hη isPreconnected_connectedComponentIn hXsub hx
    have hunit : I * ((d.η₀ : ℂ) + 1) + 1 ∈ BuOf d B :=
      hHpos_Bu (by rw [Set.mem_ofPred_eq, him_upl]; linarith)
    have hbase : I * ((d.η₀ : ℂ) + 1) ∈ {u : ℂ | u + 1 ∈ BuOf d B} := by
      rw [Set.mem_ofPred_eq]
      exact hunit
    have hpre : IsPreconnected {u : ℂ | u + 1 ∈ BuOf d B} := by
      have hS2 : {u : ℂ | u + 1 ∈ BuOf d B} = (fun z : ℂ => z - 1) '' BuOf d B := by
        ext u
        constructor
        · intro hu
          exact ⟨u + 1, hu, by ring⟩
        · rintro ⟨z, hz, rfl⟩
          simpa using hz
      rw [hS2]
      exact isPreconnected_connectedComponentIn.image _ (continuous_sub_right 1).continuousOn
    have hsub : {u : ℂ | u + 1 ∈ BuOf d B} ⊆ BuOf d B :=
      hpre.subset_connectedComponentIn hbase hshift
    exact hsub (by rw [Set.mem_ofPred_eq]; simpa using hw)
  -- `T`-invariance of `Bl`
  have hBl_add : ∀ w : ℂ, w ∈ BlOf d B → w + 1 ∈ BlOf d B := by
    intro w hw
    have hXsub : BlOf d B ⊆ Btil d B := connectedComponentIn_subset _ _
    have hshift : (fun z : ℂ => z + 1) '' BlOf d B ⊆ Btil d B := by
      rintro u ⟨z, hz, rfl⟩
      exact Btil_add_one d hB (hXsub hz)
    have hpre : IsPreconnected ((fun z : ℂ => z + 1) '' BlOf d B) :=
      isPreconnected_connectedComponentIn.image _ (continuous_add_const 1).continuousOn
    have hunit : -(I * ((d.η₀ : ℂ) + 1)) - 1 ∈ BlOf d B :=
      hHneg_Bl (by rw [Set.mem_ofPred_eq, him_lmin]; linarith)
    have hbase : -(I * ((d.η₀ : ℂ) + 1)) ∈ (fun z : ℂ => z + 1) '' BlOf d B :=
      ⟨-(I * ((d.η₀ : ℂ) + 1)) - 1, hunit, by ring⟩
    exact hpre.subset_connectedComponentIn hbase hshift ⟨w, hw, rfl⟩
  have hBl_sub : ∀ w : ℂ, w ∈ BlOf d B → w - 1 ∈ BlOf d B := by
    intro w hw
    have hXsub : BlOf d B ⊆ Btil d B := connectedComponentIn_subset _ _
    have hx : (BlOf d B ∩ {w : ℂ | η < |w.im|}).Nonempty :=
      ⟨-(I * (((|d.η₀| + |η| + 1 : ℝ)) : ℂ)), hHneg_Bl hw1_Hl, hw1_abs_l⟩
    have hshift : {u : ℂ | u + 1 ∈ BlOf d B} ⊆ Btil d B :=
      shift_subset_Btil d hB hgerm hη isPreconnected_connectedComponentIn hXsub hx
    have hunit : -(I * ((d.η₀ : ℂ) + 1)) + 1 ∈ BlOf d B :=
      hHneg_Bl (by rw [Set.mem_ofPred_eq, him_lpl]; linarith)
    have hbase : -(I * ((d.η₀ : ℂ) + 1)) ∈ {u : ℂ | u + 1 ∈ BlOf d B} := by
      rw [Set.mem_ofPred_eq]
      exact hunit
    have hpre : IsPreconnected {u : ℂ | u + 1 ∈ BlOf d B} := by
      have hS2 : {u : ℂ | u + 1 ∈ BlOf d B} = (fun z : ℂ => z - 1) '' BlOf d B := by
        ext u
        constructor
        · intro hu
          exact ⟨u + 1, hu, by ring⟩
        · rintro ⟨z, hz, rfl⟩
          simpa using hz
      rw [hS2]
      exact isPreconnected_connectedComponentIn.image _ (continuous_sub_right 1).continuousOn
    have hsub : {u : ℂ | u + 1 ∈ BlOf d B} ⊆ BlOf d B :=
      hpre.subset_connectedComponentIn hbase hshift
    exact hsub (by rw [Set.mem_ofPred_eq]; simpa using hw)
  refine ⟨hBu_open, hBl_open, ?_, ?_, hHpos_Bu, hHneg_Bl, ?_⟩
  · intro w
    exact ⟨hBu_add w, fun hw => by
      have := hBu_sub (w + 1) hw
      simpa using this⟩
  · intro w
    exact ⟨hBl_add w, fun hw => by
      have := hBl_sub (w + 1) hw
      simpa using this⟩
  · intro w hw
    have hw' : w ∈ Btil d B := by
      rcases hw with hw | hw
      · exact connectedComponentIn_subset _ _ hw
      · exact connectedComponentIn_subset _ _ hw
    exact ⟨hw'.1, hBbasin hw'.2⟩

end

end Work.HornTopo
