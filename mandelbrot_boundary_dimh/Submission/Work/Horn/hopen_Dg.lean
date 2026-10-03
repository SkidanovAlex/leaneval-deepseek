import Mathlib
import Submission.Work.Horn.germF0_base

/-!
# `Work.Horn.hopen_Dg` — the pushed-down horn map is open on its domain `D_g`

Shishikura's Prop. 5.3/Lemma 5.4 setup: `f₀ ∈ 𝓕₀` with §4.1 data `d`, `B` a nonempty immediate
parabolic basin, `BuOf d B`/`BlOf d B` the two `T`-invariant components of `φ₀⁻¹(B) ∩ Dφ` (Prop.
5.3), and

  `D_g = {0} ∪ π(B̃ᵘ ∪ B̃ˡ)`,   `g = pushdown Ẽ`,   `Ẽ = Φ₀ ∘ φ₀`.

The claim is that `g` is *open at every point of* `D_g`.  Equivalently (via Mathlib's
`AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux`) that `g` is **nowhere locally constant**
on `D_g`: a holomorphic function on a preconnected open set which is not locally constant at a point
maps neighbourhoods of every point of that set to neighbourhoods of the image.

`D_g = ({0} ∪ π(B̃ᵘ)) ⊔ π(B̃ˡ)` splits into two clopen pieces, so the local constancy has to be
excluded on each piece separately:

* at `0`: `g` has derivative `1` there (`Work.Horn.MandelDim.deriv_pushdown_E`), so `g` is not
  locally constant;
* on `π(B̃ᵘ)` (resp. `π(B̃ˡ)`): if `g ≡ c` on a neighbourhood of `π w` with `w ∈ B̃ᵘ`, then by the
  identity theorem `g ≡ c` on all of the preconnected open set `π(B̃ᵘ)`, whence
  `π(Ẽ u) = c` for **every** `u ∈ B̃ᵘ`.  But `π(a) = π(b)` forces `a.im = b.im`
  (`MandelDim.piExp_eq_iff`), while the normalization at the upper end `Ẽ u - u → 0`
  (`ParabData.E_upper`) makes `(Ẽ u).im` unbounded above on the half plane `{Im > η₀} ⊆ B̃ᵘ`
  (`not_exists_piExp_const_upper`) — contradiction.  At the lower end the same argument with
  `Ẽ u - u → cl` (`ParabData.E_lower`) and `{Im < -η₀} ⊆ B̃ˡ` (`not_exists_piExp_const_lower`).
-/

namespace Work.Horn

open Set Filter
open scoped Filter

noncomputable section

/-- `π a = π b` forces equal imaginary parts (the `ℤ`-action is by horizontal translations). -/
lemma im_eq_of_piExp_eq {a b : ℂ} (h : MandelDim.piExp a = MandelDim.piExp b) : a.im = b.im := by
  obtain ⟨k, hk⟩ := MandelDim.piExp_eq_iff.mp h
  rw [hk, Complex.add_im, Complex.intCast_im, add_zero]

/-- **The upper end forbids a constant `π ∘ Ẽ`.**  If `Ẽ w - w → L` along the upper end `Im w → ∞`
and `S` contains the half plane `{η < Im w}`, then `π(Ẽ u)` is not constant on `S`: two points
`u₀ ∈ S` and `v ∈ S` with `Im v` much larger than `Im u₀` have `(Ẽ v).im` close to `Im v` (hence
much larger than `(Ẽ u₀).im`) and at the same time equal to `(Ẽ u₀).im` (since `π` of both is the
constant `c`). -/
lemma not_exists_piExp_const_upper {E : ℂ → ℂ} {S : Set ℂ} {η : ℝ} {L : ℂ}
    (hE : Tendsto (fun w => E w - w) MandelDim.upperEnd (nhds L))
    (hS : {w : ℂ | η < w.im} ⊆ S) :
    ¬ ∃ c, ∀ u ∈ S, MandelDim.piExp (E u) = c := by
  rintro ⟨c, hc⟩
  set B : ℝ := ‖L‖ + 1 with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have h1 : ∀ᶠ w in MandelDim.upperEnd, ‖E w - w‖ < B := by
    have h := (Metric.tendsto_nhds.mp hE) 1 (by norm_num)
    filter_upwards [h] with w hw
    have h2 : ‖(E w - w - L) + L‖ = ‖E w - w‖ := by rw [sub_add_cancel]
    rw [← h2]
    calc ‖(E w - w - L) + L‖ ≤ ‖E w - w - L‖ + ‖L‖ := norm_add_le _ _
      _ = dist (E w - w) L + ‖L‖ := by rw [dist_eq_norm]
      _ < 1 + ‖L‖ := by linarith
      _ = B := by rw [hB]; ring
  rw [MandelDim.upperEnd, Filter.eventually_comap] at h1
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp h1
  set K : ℝ := max η R with hK
  have hKη : η ≤ K := by rw [hK]; exact le_max_left η R
  have hKR : R ≤ K := by rw [hK]; exact le_max_right η R
  set u₀ : ℂ := ((K + 1 : ℝ) : ℂ) * Complex.I with hu₀
  have hu₀im : u₀.im = K + 1 := by rw [hu₀]; simp [Complex.mul_im]
  have hu₀S : u₀ ∈ S := hS (by show η < u₀.im; rw [hu₀im]; linarith)
  set M : ℝ := max (E u₀).im K + B + 2 with hM
  have hMK : K + B + 2 ≤ M := by rw [hM]; linarith [le_max_right (E u₀).im K]
  have hMu : (E u₀).im + B + 2 ≤ M := by rw [hM]; linarith [le_max_left (E u₀).im K]
  set v : ℂ := (M : ℂ) * Complex.I with hv
  have hvim : v.im = M := by rw [hv]; simp [Complex.mul_im]
  have hvS : v ∈ S := hS (by show η < v.im; rw [hvim]; linarith)
  have hvR : R ≤ v.im := by rw [hvim]; linarith
  have hbound : ‖E v - v‖ < B := hR v.im hvR v rfl
  have heq : (E v).im = (E u₀).im := im_eq_of_piExp_eq (by rw [hc v hvS, hc u₀ hu₀S])
  have h3 : (E v - v).im = (E v).im - v.im := Complex.sub_im _ _
  have h4 : |(E v - v).im| ≤ ‖E v - v‖ := Complex.abs_im_le_norm _
  rw [h3] at h4
  have h5 : -B < (E v).im - M := by
    have := (abs_lt.mp (lt_of_le_of_lt h4 hbound)).1
    rw [hvim] at this
    exact this
  linarith

/-- **The lower end forbids a constant `π ∘ Ẽ`** — mirror image of `not_exists_piExp_const_upper`,
with `Ẽ w - w → L` along `Im w → -∞` and `S ⊇ {Im < -η}`. -/
lemma not_exists_piExp_const_lower {E : ℂ → ℂ} {S : Set ℂ} {η : ℝ} {L : ℂ}
    (hE : Tendsto (fun w => E w - w) MandelDim.lowerEnd (nhds L))
    (hS : {w : ℂ | w.im < -η} ⊆ S) :
    ¬ ∃ c, ∀ u ∈ S, MandelDim.piExp (E u) = c := by
  rintro ⟨c, hc⟩
  set B : ℝ := ‖L‖ + 1 with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have h1 : ∀ᶠ w in MandelDim.lowerEnd, ‖E w - w‖ < B := by
    have h := (Metric.tendsto_nhds.mp hE) 1 (by norm_num)
    filter_upwards [h] with w hw
    have h2 : ‖(E w - w - L) + L‖ = ‖E w - w‖ := by rw [sub_add_cancel]
    rw [← h2]
    calc ‖(E w - w - L) + L‖ ≤ ‖E w - w - L‖ + ‖L‖ := norm_add_le _ _
      _ = dist (E w - w) L + ‖L‖ := by rw [dist_eq_norm]
      _ < 1 + ‖L‖ := by linarith
      _ = B := by rw [hB]; ring
  rw [MandelDim.lowerEnd, Filter.eventually_comap] at h1
  obtain ⟨R, hR⟩ := Filter.eventually_atBot.mp h1
  set K : ℝ := min (-η) R with hK
  have hKη : K ≤ -η := by rw [hK]; exact min_le_left (-η) R
  have hKR : K ≤ R := by rw [hK]; exact min_le_right (-η) R
  set u₀ : ℂ := ((K - 1 : ℝ) : ℂ) * Complex.I with hu₀
  have hu₀im : u₀.im = K - 1 := by rw [hu₀]; simp [Complex.mul_im]
  have hu₀S : u₀ ∈ S := hS (by show u₀.im < -η; rw [hu₀im]; linarith)
  set M : ℝ := min (E u₀).im K - B - 2 with hM
  have hMK : M ≤ K - B - 2 := by rw [hM]; linarith [min_le_right (E u₀).im K]
  have hMu : M ≤ (E u₀).im - B - 2 := by rw [hM]; linarith [min_le_left (E u₀).im K]
  set v : ℂ := (M : ℂ) * Complex.I with hv
  have hvim : v.im = M := by rw [hv]; simp [Complex.mul_im]
  have hvS : v ∈ S := hS (by show v.im < -η; rw [hvim]; linarith)
  have hvR : v.im ≤ R := by rw [hvim]; linarith
  have hbound : ‖E v - v‖ < B := hR v.im hvR v rfl
  have heq : (E v).im = (E u₀).im := im_eq_of_piExp_eq (by rw [hc v hvS, hc u₀ hu₀S])
  have h3 : (E v - v).im = (E v).im - v.im := Complex.sub_im _ _
  have h4 : |(E v - v).im| ≤ ‖E v - v‖ := Complex.abs_im_le_norm _
  rw [h3] at h4
  have h5 : (E v).im - M < B := by
    have := (abs_lt.mp (lt_of_le_of_lt h4 hbound)).2
    rw [hvim] at this
    exact this
  linarith

/-- **`g = pushdown Ẽ` is open at every point of `D_g = {0} ∪ π(B̃ᵘ ∪ B̃ˡ)`** (the `hopen`
hypothesis of `Work.Horn.flower_petals_Dg`).  See the module docstring for the argument. -/
theorem hopen_Dg {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) :
    ∀ z ∈ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)),
      ∀ U ∈ nhds z, MandelDim.pushdown d.E '' U ∈ nhds (MandelDim.pushdown d.E z) := by
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hup, hlo, hsub⟩ :=
    Work.HornTopo.horn_topo f₀ D₀ B c d hsetup
  obtain ⟨cl, hcl⟩ := d.E_lower
  have hDgO : IsOpen (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hgholo : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))) :=
    pushdown_E_differentiableOn d d.η₀ (MandelDim.BuOf d B) (MandelDim.BlOf d B)
      hBuO hBlO hBuT hBlT hsub hup hlo
  have hcont : Continuous MandelDim.piExp := by unfold MandelDim.piExp; continuity
  -- `Ẽ` is `T`-equivariant on each component (Shishikura's `T w = w + 1`)
  have hEaddU : ∀ u ∈ MandelDim.BuOf d B, d.E (u + 1) = d.E u + 1 := fun u hu =>
    MandelDim.ParabData.E_add_one d (hsub (Or.inl hu)) (hsub (Or.inl ((hBuT u).mp hu)))
  have hEaddL : ∀ u ∈ MandelDim.BlOf d B, d.E (u + 1) = d.E u + 1 := fun u hu =>
    MandelDim.ParabData.E_add_one d (hsub (Or.inr hu)) (hsub (Or.inr ((hBlT u).mp hu)))
  -- the key point: `g` is nowhere locally constant on its domain
  have key : ∀ ζ ∈ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)),
      ¬ (MandelDim.pushdown d.E =ᶠ[nhds ζ] fun _ => MandelDim.pushdown d.E ζ) := by
    intro ζ hζ hconst
    rcases hζ with rfl | ⟨w, hw, rfl⟩
    · -- `ζ = 0`: the derivative there is `1`
      have hd : deriv (MandelDim.pushdown d.E) 0 = 0 := by
        rw [hconst.deriv_eq]
        simp
      rw [MandelDim.deriv_pushdown_E d] at hd
      exact one_ne_zero hd
    · rcases hw with hw | hw
      · -- `ζ = π w`, `w ∈ B̃ᵘ`: `g ≡ const` on `π(B̃ᵘ)`, hence `π ∘ Ẽ` is constant on `B̃ᵘ`
        have hsubU : MandelDim.piExp '' (MandelDim.BuOf d B) ⊆
            insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) :=
          (Set.image_mono Set.subset_union_left).trans (Set.subset_insert _ _)
        have hana : AnalyticOnNhd ℂ (MandelDim.pushdown d.E)
            (MandelDim.piExp '' (MandelDim.BuOf d B)) :=
          (hgholo.analyticOnNhd hDgO).mono hsubU
        have hpre : IsPreconnected (MandelDim.piExp '' (MandelDim.BuOf d B)) :=
          (isPreconnected_connectedComponentIn).image _ hcont.continuousOn
        have hmem : MandelDim.piExp w ∈ MandelDim.piExp '' (MandelDim.BuOf d B) := ⟨w, hw, rfl⟩
        have hEqOn := hana.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hpre hmem hconst
        refine not_exists_piExp_const_upper (E := d.E) (S := MandelDim.BuOf d B)
          (η := d.η₀) d.E_upper hup ⟨MandelDim.piExp (d.E w), ?_⟩
        intro u hu
        have h1 : MandelDim.pushdown d.E (MandelDim.piExp u) =
            MandelDim.pushdown d.E (MandelDim.piExp w) := hEqOn ⟨u, hu, rfl⟩
        rw [MandelDim.pushdown_piExp hBuT (fun a ha _ => hEaddU a ha) hu,
            MandelDim.pushdown_piExp hBuT (fun a ha _ => hEaddU a ha) hw] at h1
        exact h1
      · -- `ζ = π w`, `w ∈ B̃ˡ`: the same argument at the lower end
        have hsubL : MandelDim.piExp '' (MandelDim.BlOf d B) ⊆
            insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) :=
          (Set.image_mono Set.subset_union_right).trans (Set.subset_insert _ _)
        have hana : AnalyticOnNhd ℂ (MandelDim.pushdown d.E)
            (MandelDim.piExp '' (MandelDim.BlOf d B)) :=
          (hgholo.analyticOnNhd hDgO).mono hsubL
        have hpre : IsPreconnected (MandelDim.piExp '' (MandelDim.BlOf d B)) :=
          (isPreconnected_connectedComponentIn).image _ hcont.continuousOn
        have hmem : MandelDim.piExp w ∈ MandelDim.piExp '' (MandelDim.BlOf d B) := ⟨w, hw, rfl⟩
        have hEqOn := hana.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hpre hmem hconst
        refine not_exists_piExp_const_lower (E := d.E) (S := MandelDim.BlOf d B)
          (η := d.η₀) hcl hlo ⟨MandelDim.piExp (d.E w), ?_⟩
        intro u hu
        have h1 : MandelDim.pushdown d.E (MandelDim.piExp u) =
            MandelDim.pushdown d.E (MandelDim.piExp w) := hEqOn ⟨u, hu, rfl⟩
        rw [MandelDim.pushdown_piExp hBlT (fun a ha _ => hEaddL a ha) hu,
            MandelDim.pushdown_piExp hBlT (fun a ha _ => hEaddL a ha) hw] at h1
        exact h1
  intro z hz U hU
  have hAn : AnalyticAt ℂ (MandelDim.pushdown d.E) z := (hgholo.analyticOnNhd hDgO) z hz
  rcases AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux hAn with hcc | hop
  · exact absurd hcc (key z hz)
  · have hmem : MandelDim.pushdown d.E '' U ∈ Filter.map (MandelDim.pushdown d.E) (nhds z) :=
      Filter.mem_map.mpr (Filter.mem_of_superset hU (Set.subset_preimage_image _ U))
    exact (Filter.le_def.mp hop) _ hmem

end

end Work.Horn
