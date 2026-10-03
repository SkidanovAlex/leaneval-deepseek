import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.HornTopo.horn_topo
import Submission.Work.Horn.HB.Psi_inverse
import Submission.Work.Horn.HB.isCompact_component_inter_preimage

/-! Guidance from the project lead (the requester):

LEAD DESIGN (read Submission/Work/Horn/HB/DESIGN.md). Piece HB1 of horn_basin: the exact route.
Setup: hS gives f₀ a parabolic germ, B an immediate basin (f₀ : B → B proper, B ⊆ f₀ '' B), c ∈ B the unique critical point in B. ParabData fields: Ωp open, Ωp ⊆ B (Work.HornTopo omega_subset_B or similar), f₀(Ωp) ⊆ Ωp (Ωp_maps), Φ_holo/Φ_abel on the basin (Φ(f₀ z) = Φ z + 1), Φ_inj on Ωp, Φ_image (∀ b ∃ C: {Re > C, |Im| ≤ b} ⊆ Φ(Ωp)), basin_enter (every basin point eventually enters Ωp).
1. Ψ := inverse of Φ on Ωp. Φ|Ωp is injective holomorphic, hence an open embedding, so Ψ is continuous on the open set Φ(Ωp). U is bounded, so by Φ_image there is m₀ with U + m ⊆ Φ(Ωp) for all m ≥ m₀.
2. Y := connectedComponentIn (B ∩ Φ⁻¹U) z. Let Y_m := {y ∈ Y | f₀^[m] y ∈ Ωp} for m ≥ m₀.
   - Y_m is OPEN (f₀^[m] is continuous on B).
   - Y_m is CLOSED IN Y: if y_k → y with y_k ∈ Y_m, then f^m y_k = Ψ(Φ y_k + m) by Φ_abel iterated + Φ_inj. Ψ and Φ are continuous, so f^m y = Ψ(Φ y + m) ∈ Ωp.
   - The Y_m are increasing (Ωp_maps) and their union is Y (basin_enter).
   Y is connected, so Y = Y_m for one m ≥ m₀.
3. Then Y ⊆ S := B ∩ (f₀^[m])⁻¹(W) with W := Ψ(U + m) ⊆ Ωp ⊆ B, which is connected and open. Also S ⊆ B ∩ Φ⁻¹U, since Φ = Φ∘f^m − m. So Y = connectedComponentIn S z.
4. f₀^[m] is proper on B (iterate the IsImmediateBasin properness clause). Apply Work.BasinSC.Tower.isCompact_connectedComponentIn_inter_preimage with f := f₀^[m], W, V := S and K' := Ψ(K + m) (compact, ⊆ W). Finally Y ∩ Φ⁻¹K = Y ∩ (f^m)⁻¹(Ψ(K+m)).
Do NOT use the refuted properness routes of NOTES_SESSION17 §6; this lemma is purely about Φ on B. Split into children if large (e.g. step 1 as a lemma Psi_continuous, step 2 as Y_eq_Ym).

Implementation as carried out here (steps 1-4 above, with `shift m U = {w | w - m ∈ U}` playing
the role of `U + m`, so that the `m`-translation is expressed by subtraction):

* step 1 is the separate lemma `Work.Horn.HB.Psi_inverse` (imported);
* the topological core of step 4 is the separate lemma
  `Work.Horn.HB.isCompact_component_inter_preimage` (imported), the tower lemma with the weaker
  hypothesis `K ⊆ W` on the compact set;
* everything in between is proved below, in particular the `Ψ`-identity `f^m y = Ψ (Φ y + m)` for
  `y ∈ Y` (via `Φ_inj`), which upgrades the relative-closedness of `Y_m` to the covering step.
-/

open MandelDim Set Metric Filter Topology

namespace Work.Horn.HB

/-- The parabolic basin is open (the witness `U ∈ 𝓝 z` may be replaced by its interior at every
point of `U`). -/
private lemma isOpen_parabolicBasin (f : ℂ → ℂ) (D : Set ℂ) :
    IsOpen (ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hmap, hunif⟩
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  exact Filter.mem_of_superset (hVopen.mem_nhds hzV) fun y hy =>
    ⟨V, hVopen.mem_nhds hy, fun n => (hmap n).mono hVU Subset.rfl, hunif.mono hVU⟩

/-- `U` translated by `-m`. -/
private def shift (m : ℕ) (U : Set ℂ) : Set ℂ := {w : ℂ | w - m ∈ U}

private lemma isOpen_shift {U : Set ℂ} (hU : IsOpen U) (m : ℕ) : IsOpen (shift m U) :=
  hU.preimage (continuous_id.sub continuous_const)

/-- Properness is preserved by iteration, for a self-map of a set. -/
private lemma isCompact_inter_iterate_preimage {f : ℂ → ℂ} {B : Set ℂ} (hmap : MapsTo f B B)
    (hproper : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L)) (m : ℕ) :
    ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ (f^[m]) ⁻¹' L) := by
  have hmapit : ∀ k : ℕ, MapsTo (f^[k]) B B := by
    intro k
    induction k with
    | zero => intro y hy; exact hy
    | succ j ih => intro y hy; rw [Function.iterate_succ_apply']; exact hmap (ih hy)
  induction m with
  | zero =>
      intro L hLB hLc
      rw [Function.iterate_zero, Set.preimage_id, inter_eq_right.mpr hLB]
      exact hLc
  | succ k ih =>
      intro L hLB hLc
      have h1 : B ∩ (f^[k+1]) ⁻¹' L = B ∩ (f^[k]) ⁻¹' (B ∩ f ⁻¹' L) := by
        ext y
        simp only [mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨hyB, hyL⟩
          rw [Function.iterate_succ_apply'] at hyL
          exact ⟨hyB, hmapit k hyB, hyL⟩
        · rintro ⟨hyB, hyW, hyL⟩
          exact ⟨hyB, by rw [Function.iterate_succ_apply']; exact hyL⟩
      rw [h1]
      exact ih (B ∩ f ⁻¹' L) inter_subset_left (hproper L hLB hLc)

theorem Phi_component_proper {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hS : MandelDim.IsF0Setup f₀ D₀ B c) {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hUb : Bornology.IsBounded U) {z : ℂ} (hzB : z ∈ B) (hzU : d.Φ z ∈ U) :
    ∀ K ⊆ U, IsCompact K →
      IsCompact (connectedComponentIn (B ∩ d.Φ ⁻¹' U) z ∩ d.Φ ⁻¹' K) := by
  have hΩB : d.Ωp ⊆ B := Work.HornTopo.omega_subset_B hS d
  obtain ⟨hgerm, hIB, hcB, hcrit, huniq⟩ := hS
  have hBopen : IsOpen B := hIB.1
  have hBbasin : B ⊆ ParabolicBasin f₀ D₀ := hIB.2.2.1
  have hmap : MapsTo f₀ B B := hIB.2.2.2.2.1
  have hBproper : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f₀ ⁻¹' L) := hIB.2.2.2.2.2.2
  have hBsubD : B ⊆ D₀ := by
    intro y hy
    obtain ⟨U', hU', hiter, -⟩ := hBbasin hy
    simpa using hiter 0 (mem_of_mem_nhds hU')
  have hDopen : IsOpen D₀ := hgerm.1
  have hfdiff : DifferentiableOn ℂ f₀ D₀ := hgerm.2.2.1
  have hfcont : ∀ y ∈ B, ContinuousAt f₀ y := fun y hy =>
    (hfdiff.differentiableAt (hDopen.mem_nhds (hBsubD hy))).continuousAt
  have hΦcont : ∀ y ∈ B, ContinuousAt d.Φ y := fun y hy =>
    (d.Φ_holo.differentiableAt ((isOpen_parabolicBasin f₀ D₀).mem_nhds (hBbasin hy))).continuousAt
  have hmapit : ∀ k : ℕ, MapsTo (f₀^[k]) B B := by
    intro k
    induction k with
    | zero => intro y hy; exact hy
    | succ j ih => intro y hy; rw [Function.iterate_succ_apply']; exact hmap (ih hy)
  have hfitcont : ∀ k : ℕ, ∀ y ∈ B, ContinuousAt (f₀^[k]) y := by
    intro k
    induction k with
    | zero => intro y hy; simpa using continuousAt_id
    | succ j ih =>
        intro y hy
        have hcomp := (hfcont ((f₀^[j]) y) (hmapit j hy)).comp (ih y hy)
        rw [show (f₀^[j+1]) = (f₀ ∘ (f₀^[j])) from
          funext fun x => Function.iterate_succ_apply' f₀ j x]
        exact hcomp
  have hiterΩ : ∀ k : ℕ, MapsTo (f₀^[k]) d.Ωp d.Ωp := by
    intro k
    induction k with
    | zero => intro y hy; exact hy
    | succ j ih => intro y hy; rw [Function.iterate_succ_apply']; exact d.Ωp_maps (ih hy)
  have habel : ∀ k : ℕ, ∀ y ∈ B, d.Φ ((f₀^[k]) y) = d.Φ y + k := by
    intro k
    induction k with
    | zero => intro y hy; simp
    | succ j ih =>
        intro y hy
        rw [Function.iterate_succ_apply', d.Φ_abel ((f₀^[j]) y) (hBbasin (hmapit j hy)), ih y hy]
        push_cast
        ring
  obtain ⟨Ψ, hΨ, hΨ_cont⟩ := Psi_inverse d
  -- the translated set `U + m` lies in `Φ '' Ωp` for all large `m`
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ u ∈ U, ‖u‖ ≤ b := by
    obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hUb
    refine ⟨R + ‖d.Φ z‖, fun u hu => ?_⟩
    have h1 : ‖u - d.Φ z‖ ≤ R := by
      have h2 := hR hu hzU
      rwa [dist_eq_norm] at h2
    calc ‖u‖ ≤ ‖u - d.Φ z‖ + ‖d.Φ z‖ := by
          simpa using norm_add_le (u - d.Φ z) (d.Φ z)
      _ ≤ R + ‖d.Φ z‖ := by linarith
  obtain ⟨C, hC⟩ := d.Φ_image b
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (C + b)
  obtain ⟨nz, hnz⟩ := d.basin_enter z (hBbasin hzB) fun n => d.orbit_avoid z (hBbasin hzB) n
  let m : ℕ := max m₀ nz
  have hm₀m : C + b < (m : ℝ) := lt_of_lt_of_le hm₀ (by exact_mod_cast le_max_left m₀ nz)
  have hnzm : nz ≤ m := le_max_right m₀ nz
  have h_fmz : (f₀^[m]) z ∈ d.Ωp := by
    have hsplit : m = (m - nz) + nz := (Nat.sub_add_cancel hnzm).symm
    rw [hsplit, Function.iterate_add_apply]
    exact hiterΩ (m - nz) hnz
  have hUm_sub : shift m U ⊆ d.Φ '' d.Ωp := by
    intro w hw
    have hwU : w - m ∈ U := hw
    have hnorm : ‖w - m‖ ≤ b := hb _ hwU
    have hre : C < w.re := by
      have h2 := Complex.abs_re_le_norm (w - m)
      rw [abs_le] at h2
      have h3 : (w - m).re = w.re - (m : ℝ) := by simp
      linarith [h2.1]
    have him : |w.im| ≤ b := by
      have h3 : (w - m).im = w.im := by simp
      calc |w.im| = |(w - m).im| := by rw [h3]
        _ ≤ ‖w - m‖ := Complex.abs_im_le_norm _
        _ ≤ b := hnorm
    obtain ⟨y, hyΩ, hyw⟩ := hC w hre him
    exact ⟨y, hyΩ, hyw⟩
  let Wv : Set ℂ := d.Ωp ∩ d.Φ ⁻¹' shift m U
  let S : Set ℂ := B ∩ (f₀^[m]) ⁻¹' Wv
  let Y : Set ℂ := connectedComponentIn (B ∩ d.Φ ⁻¹' U) z
  have hΩcont : ∀ y ∈ d.Ωp, ContinuousAt d.Φ y := fun y hy => hΦcont y (hΩB hy)
  have hWv_open : IsOpen Wv := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyΩ, hyΦ⟩
    exact Filter.inter_mem (d.Ωp_open.mem_nhds hyΩ)
      ((hΩcont y hyΩ).preimage_mem_nhds ((isOpen_shift hUo m).mem_nhds hyΦ))
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyB, hyW⟩
    exact Filter.inter_mem (hBopen.mem_nhds hyB)
      ((hfitcont m y hyB).preimage_mem_nhds (hWv_open.mem_nhds hyW))
  have hzS : z ∈ S := by
    refine ⟨hzB, ?_, ?_⟩
    · exact h_fmz
    · have h : d.Φ ((f₀^[m]) z) - m ∈ U := by
        rw [habel m z hzB, add_sub_cancel_right]
        exact hzU
      exact h
  have hzY : z ∈ Y := mem_connectedComponentIn ⟨hzB, hzU⟩
  have hYpre : IsPreconnected Y := isPreconnected_connectedComponentIn
  -- the crucial relative-closedness: a limit of points of `S` inside `Y` is again in `S`
  have hclosureS : Y ∩ closure S ⊆ S := by
    rintro y ⟨hyY, hycl⟩
    have hyBs : y ∈ B ∩ d.Φ ⁻¹' U := connectedComponentIn_subset _ _ hyY
    have hyB : y ∈ B := hyBs.1
    have hyU : d.Φ y ∈ U := hyBs.2
    obtain ⟨yseq, hyseq, hlim⟩ := mem_closure_iff_seq_limit.mp hycl
    have hseq_Um : ∀ n, d.Φ (yseq n) + m ∈ shift m U := by
      intro n
      have h1 : d.Φ ((f₀^[m]) (yseq n)) ∈ shift m U := (hyseq n).2.2
      rwa [habel m (yseq n) (hyseq n).1] at h1
    have hseq_Img : ∀ n, d.Φ (yseq n) + m ∈ d.Φ '' d.Ωp := fun n => hUm_sub (hseq_Um n)
    have hseq_id : ∀ n, (f₀^[m]) (yseq n) = Ψ (d.Φ (yseq n) + m) := by
      intro n
      have h1 : d.Φ (Ψ (d.Φ (yseq n) + m)) = d.Φ (yseq n) + m := (hΨ _ (hseq_Img n)).2
      have h2 : d.Φ ((f₀^[m]) (yseq n)) = d.Φ (yseq n) + m := habel m (yseq n) (hyseq n).1
      exact d.Φ_inj (hyseq n).2.1 (hΨ _ (hseq_Img n)).1 (by rw [h2, h1])
    have hmem_y : d.Φ y + m ∈ d.Φ '' d.Ωp := hUm_sub (by
      have h : d.Φ y + m - m ∈ U := by rw [add_sub_cancel_right]; exact hyU
      exact h)
    have hlimΦ : Tendsto (fun n => d.Φ (yseq n) + m) atTop (𝓝 (d.Φ y + m)) :=
      ((hΦcont y hyB).tendsto.comp hlim).add_const (m : ℂ)
    have hwit : Tendsto Ψ (𝓝[d.Φ '' d.Ωp] (d.Φ y + m)) (𝓝 (Ψ (d.Φ y + m))) :=
      hΨ_cont.continuousWithinAt hmem_y
    have hlimΨ : Tendsto (fun n => Ψ (d.Φ (yseq n) + m)) atTop (𝓝 (Ψ (d.Φ y + m))) := by
      refine hwit.comp ?_
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hlimΦ, Filter.Eventually.of_forall hseq_Img⟩
    have hlimf : Tendsto (fun n => (f₀^[m]) (yseq n)) atTop (𝓝 ((f₀^[m]) y)) :=
      (hfitcont m y hyB).tendsto.comp hlim
    have heq : (f₀^[m]) y = Ψ (d.Φ y + m) :=
      (tendsto_nhds_unique hlimΨ (hlimf.congr' (Filter.Eventually.of_forall hseq_id))).symm
    refine ⟨hyB, ?_, ?_⟩
    · rw [heq]
      exact (hΨ _ hmem_y).1
    · have h : d.Φ ((f₀^[m]) y) - m ∈ U := by
        rw [habel m y hyB, add_sub_cancel_right]
        exact hyU
      exact h
  have hYS : Y ⊆ S := by
    have hsub : Y ⊆ S ∪ (closure S)ᶜ := by
      intro y hy
      by_cases hyS : y ∈ S
      · exact Or.inl hyS
      · refine Or.inr fun hycl => hyS ?_
        exact hclosureS ⟨hy, hycl⟩
    rcases IsPreconnected.subset_or_subset (s := Y) (u := S) (v := (closure S)ᶜ)
      hS_open isClosed_closure.isOpen_compl
        (disjoint_compl_right.mono_right (compl_subset_compl.mpr subset_closure)) hsub hYpre with h | h
    · exact h
    · exact absurd (h hzY) (by simp [subset_closure hzS])
  have hSsub : S ⊆ B ∩ d.Φ ⁻¹' U := by
    rintro y ⟨hyB, hyW⟩
    refine ⟨hyB, ?_⟩
    have h1 : d.Φ ((f₀^[m]) y) ∈ shift m U := hyW.2
    rw [habel m y hyB] at h1
    have h2 : d.Φ y + m - m ∈ U := h1
    rw [add_sub_cancel_right] at h2
    exact h2
  have hYcomp : connectedComponentIn S z = Y :=
    subset_antisymm
      (show connectedComponentIn S z ⊆ Y from connectedComponentIn_mono z hSsub)
      (hYpre.subset_connectedComponentIn hzY hYS)
  have hproper_m : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ (f₀^[m]) ⁻¹' L) :=
    isCompact_inter_iterate_preimage hmap hBproper m
  have hWv_subB : Wv ⊆ B := fun y hy => hΩB hy.1
  intro K hKU hKc
  let Km : Set ℂ := (fun w : ℂ => w + m) '' K
  let K' : Set ℂ := Ψ '' Km
  have hKm_sub : Km ⊆ shift m U := by
    rintro w ⟨k, hkK, rfl⟩
    have h : k + m - m ∈ U := by rw [add_sub_cancel_right]; exact hKU hkK
    exact h
  have hKm_compact : IsCompact Km :=
    show IsCompact ((fun w : ℂ => w + m) '' K) from hKc.image (continuous_add_const (m : ℂ))
  have hKm_img : Km ⊆ d.Φ '' d.Ωp := hKm_sub.trans hUm_sub
  have hK'_compact : IsCompact K' :=
    show IsCompact (Ψ '' Km) from hKm_compact.image_of_continuousOn (hΨ_cont.mono hKm_img)
  have hK'_sub : K' ⊆ Wv := by
    rintro w ⟨v, hv, rfl⟩
    refine ⟨(hΨ v (hKm_img hv)).1, ?_⟩
    have h : d.Φ (Ψ v) ∈ shift m U := by rw [(hΨ v (hKm_img hv)).2]; exact hKm_sub hv
    exact h
  have hcomp := isCompact_component_inter_preimage (f := f₀^[m]) (B := B) (W := Wv) (V := S)
    (x := z) hproper_m hWv_subB rfl K' hK'_sub hK'_compact
  have hseteq : Y ∩ (f₀^[m]) ⁻¹' K' = Y ∩ d.Φ ⁻¹' K := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hyY, hyK'⟩
      obtain ⟨v, hvKm, hv⟩ := hyK'
      obtain ⟨k, hkK, rfl⟩ := hvKm
      have hyB : y ∈ B := (connectedComponentIn_subset _ _ hyY).1
      have hmemUm : k + m ∈ shift m U := by
        have h : k + m - m ∈ U := by rw [add_sub_cancel_right]; exact hKU hkK
        exact h
      have hmemImg : k + m ∈ d.Φ '' d.Ωp := hUm_sub hmemUm
      have h1 : d.Φ (Ψ (k + m)) = k + m := (hΨ _ hmemImg).2
      have h2 : d.Φ ((f₀^[m]) y) = d.Φ y + m := habel m y hyB
      have h3 : k + m = d.Φ y + m := by rw [← h1, hv, h2]
      have h4 : k = d.Φ y := add_right_cancel h3
      exact ⟨hyY, by rw [← h4]; exact hkK⟩
    · rintro ⟨hyY, hyK⟩
      have hyBs : y ∈ B ∩ d.Φ ⁻¹' U := connectedComponentIn_subset _ _ hyY
      have hyB : y ∈ B := hyBs.1
      have hyS : y ∈ S := hYS hyY
      have hfmΩ : (f₀^[m]) y ∈ d.Ωp := hyS.2.1
      have hmemUm : d.Φ y + m ∈ shift m U := by
        have h : d.Φ y + m - m ∈ U := by rw [add_sub_cancel_right]; exact hyBs.2
        exact h
      have hmemImg : d.Φ y + m ∈ d.Φ '' d.Ωp := hUm_sub hmemUm
      have h1 : d.Φ (Ψ (d.Φ y + m)) = d.Φ y + m := (hΨ _ hmemImg).2
      have h2 : d.Φ ((f₀^[m]) y) = d.Φ y + m := habel m y hyB
      have heq : Ψ (d.Φ y + m) = (f₀^[m]) y :=
        d.Φ_inj (hΨ _ hmemImg).1 hfmΩ (by rw [h1, h2])
      exact ⟨hyY, ⟨d.Φ y + m, ⟨d.Φ y, hyK, rfl⟩, heq⟩⟩
  have hseteq' : connectedComponentIn S z ∩ (f₀^[m]) ⁻¹' K'
      = connectedComponentIn S z ∩ d.Φ ⁻¹' K := by
    rw [hYcomp]
    exact hseteq
  rw [hseteq', hYcomp] at hcomp
  exact hcomp

end Work.Horn.HB
