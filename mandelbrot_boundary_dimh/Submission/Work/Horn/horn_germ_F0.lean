import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.germ_expansion_free
import Submission.Work.Horn.isImmediateBasin_rescale
import Submission.Work.Horn.simplyConnectedSpace_rescale
import Submission.Work.Horn.immediateBasin_has_critval_free
import Submission.Work.Horn.Dg_pieces
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.fiber_infinite_in_basin
import Submission.Work.Horn.not_immediateBasin_of_connected
import Submission.Work.Horn.zero_not_mem_basin_pushdown
import Submission.Work.Horn.not_immediateBasin_of_finite_components
import Submission.Work.Horn.exists_basin_component_in_outer
import Submission.Work.Horn.basin_components_infinite
import Submission.Work.Horn.DE_T_of_phi_maps_to_D0
import Submission.Work.Horn.spreadDatum_and_basinDatum_of_componentStatement
import Submission.Work.Horn.germF0_conj1
import Submission.Work.Horn.confinement_reduction
import Submission.Work.Horn.horn_basin_thm

namespace Work.Horn

open Filter Topology
open scoped Topology

/-!
# `Work.Horn.horn_germ_F0` — Shishikura's Lemma 5.4 for the pushed-down horn map

Target: `Work.Horn.horn_germ_F0`.  Everything it needs that was already proved lives in
`Submission/Work/Horn/germF0_base.lean` (sorry-free).  This file contains

* `Work.Horn.germ_coeff_eq_zero_of_lt`, `Work.Horn.germ_exponent_unique` — the Leau–Fatou
  exponent `q` is determined by the germ `g` (the first non-vanishing Taylor coefficient of
  `g - id` is unique);
* `Work.Horn.SpreadDatum` — the SHARP form of the one remaining input: for the actual Leau–Fatou
  expansion of `g = pushdown d.E` on `D_g = {0} ∪ π(Bu ∪ Bl)`, the `q` spreads of the `q` petals
  are pairwise disjoint immediate parabolic basins of `g` on `D_g`, simply connected, with `g` not
  injective on each and with a critical point inside each;
* `Work.Horn.horn_germ_F0_of_spreadDatum` — the TARGET from `SpreadDatum`:
  * conjunct 1 (`g''(0) ≠ 0`): if `g''(0) = 0` then `germ_expansion_free` produces an expansion
    with `q ≥ 2`, while `eq_one_of_spreads` forces `q = 1` for the actual expansion — and by
    `germ_exponent_unique` the two exponents agree;
  * conjunct 2 (`InF0` after rescaling): the `q = 1` instance of `SpreadDatum` gives an immediate
    basin `B` of `g` on `D_g` that is simply connected and carries a critical point; then
    `Work.Horn.existsUnique_critPoint_germ1` gives the `∃!` clause and
    `Work.Horn.isImmediateBasin_rescale` + `Work.Horn.simplyConnectedSpace_rescale` transport the
    basin to the rescaled map.

`SpreadDatum` is NOT refutable for the actual germ (unlike a `∀ q` version: see
NOTES_GERM_F0.md §68.3 — a `∀ q` statement is refutable for `q ≥ 2`, precisely because
`Work.Horn.eq_one_of_spreads` then contradicts it).  It is the exact mathematical content of
Shishikura's `V^{(i)}_n` chain + Lemma 5.2 bookkeeping, isolated so that the rest of the
development is unconditional.
-/

/-- `(z^(q'+1))⁻¹ * z^(q'-q) = (z^(q+1))⁻¹` for `q ≤ q'`, `z ≠ 0`. -/
private lemma inv_pow_mul_eq (z : ℂ) (hz : z ≠ 0) {q q' : ℕ} (h : q ≤ q') :
    (z ^ (q' + 1))⁻¹ * z ^ (q' - q) = (z ^ (q + 1))⁻¹ := by
  have hq : z ^ (q + 1) ≠ 0 := pow_ne_zero _ hz
  have hq' : z ^ (q' + 1) ≠ 0 := pow_ne_zero _ hz
  field_simp
  rw [← pow_add]
  congr 1
  omega

/-- `G / z^(q+1) = (G / z^(q'+1)) * z^(q'-q)` for `q ≤ q'`, `z ≠ 0`. -/
private lemma div_pow_eq_div_pow_mul (z : ℂ) (hz : z ≠ 0) {q q' : ℕ} (h : q ≤ q') (G : ℂ) :
    G / z ^ (q + 1) = G / z ^ (q' + 1) * z ^ (q' - q) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, inv_pow_mul_eq z hz h]

theorem germ_coeff_eq_zero_of_lt {g : ℂ → ℂ} {q q' : ℕ} {a a' : ℂ}
    (h : Filter.Tendsto (fun z : ℂ => (g z - z - a * z ^ (q + 1)) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0))
    (h' : Filter.Tendsto (fun z : ℂ => (g z - z - a' * z ^ (q' + 1)) / z ^ (q' + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0))
    (hlt : q < q') : a = 0 := by
  have hz0 : ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz
  have hFlim : Filter.Tendsto (fun z : ℂ => (g z - z) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds a) := by
    have h1 : Filter.Tendsto (fun z : ℂ => (g z - z) / z ^ (q + 1) - a)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      refine h.congr' ?_
      filter_upwards [hz0] with z hz
      field_simp
    have h2 := h1.add (tendsto_const_nhds (x := a))
    simpa using h2
  have hGlim : Filter.Tendsto (fun z : ℂ => (g z - z) / z ^ (q' + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds a') := by
    have h1 : Filter.Tendsto (fun z : ℂ => (g z - z) / z ^ (q' + 1) - a')
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      refine h'.congr' ?_
      filter_upwards [hz0] with z hz
      field_simp
    have h2 := h1.add (tendsto_const_nhds (x := a'))
    simpa using h2
  have hzq : Filter.Tendsto (fun z : ℂ => z ^ (q' - q)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have h1 : Filter.Tendsto (fun z : ℂ => z ^ (q' - q)) (nhds (0 : ℂ))
        (nhds ((0 : ℂ) ^ (q' - q))) := tendsto_id.pow (q' - q)
    rw [zero_pow (by omega : q' - q ≠ 0)] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hprod : Filter.Tendsto (fun z : ℂ => (g z - z) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hm : Filter.Tendsto (fun z : ℂ => (g z - z) / z ^ (q' + 1) * z ^ (q' - q))
        (nhdsWithin 0 {0}ᶜ) (nhds (a' * 0)) := hGlim.mul hzq
    have hm0 : Filter.Tendsto (fun z : ℂ => (g z - z) / z ^ (q' + 1) * z ^ (q' - q))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by simpa using hm
    refine hm0.congr' ?_
    filter_upwards [hz0] with z hz
    exact (div_pow_eq_div_pow_mul z hz (le_of_lt hlt) (g z - z)).symm
  exact tendsto_nhds_unique hFlim hprod

/-- **Uniqueness of the Leau-Fatou exponent.** -/
theorem germ_exponent_unique {g : ℂ → ℂ} {q q' : ℕ} {a a' : ℂ}
    (h : Filter.Tendsto (fun z : ℂ => (g z - z - a * z ^ (q + 1)) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0))
    (h' : Filter.Tendsto (fun z : ℂ => (g z - z - a' * z ^ (q' + 1)) / z ^ (q' + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0))
    (ha : a ≠ 0) (ha' : a' ≠ 0) : q = q' := by
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · exact absurd (germ_coeff_eq_zero_of_lt h h' hlt) ha
  · exact heq
  · exact absurd (germ_coeff_eq_zero_of_lt h' h hgt) ha'

/-- **The counting step, weak form** (replaces `Work.Horn.eq_one_of_spreads` in the direction
needed here, and needs NO properness, NO simple connectivity and NO injectivity).

If all critical values of `f` on `D` coincide with the single `v`, and `B i` are pairwise disjoint
`f`-invariant subsets of `D` each containing a critical point of `f`, then there is at most one
index.  Indeed each `B i` contains the critical point's value `v` (invariance), so two distinct
indices would give two disjoint sets both containing `v`. -/
theorem eq_one_of_invariant_disjoint {f : ℂ → ℂ} {D : Set ℂ} {v : ℂ} {q : ℕ} {B : Fin q → Set ℂ}
    (hcritval : ∀ z ∈ D, deriv f z = 0 → f z = v)
    (hsub : ∀ i, B i ⊆ D)
    (hmap : ∀ i, Set.MapsTo f (B i) (B i))
    (hcrit : ∀ i, ∃ z ∈ B i, deriv f z = 0)
    (hdisj : ∀ i j : Fin q, i ≠ j → Disjoint (B i) (B j))
    (hq : 2 ≤ q) : False := by
  have hv : ∀ i, v ∈ B i := by
    intro i
    obtain ⟨z, hz, hzd⟩ := hcrit i
    rw [← hcritval z (hsub i hz) hzd]
    exact hmap i hz
  have hne : (⟨0, by omega⟩ : Fin q) ≠ ⟨1, by omega⟩ := by
    intro h
    have hval : (0 : ℕ) = 1 := by simpa using congrArg Fin.val h
    omega
  exact Set.disjoint_left.mp (hdisj ⟨0, by omega⟩ ⟨1, by omega⟩ hne)
    (hv ⟨0, by omega⟩) (hv ⟨1, by omega⟩)

/-- **The target from the two data.** -/
theorem horn_germ_F0_of_spreadDatum {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hspread : SpreadDatum (d := d) (η := η) (Bu := Bu) (Bl := Bl))
    (hbasind : BasinDatum (d := d) (η := η) (Bu := Bu) (Bl := Bl)) :
    deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 ∧
      MandelDim.InF0
        (fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) *
          MandelDim.pushdown d.E (ζ / (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2)))
        ((fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) * ζ) ''
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
  classical
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨hBuO, hBlO, _, _, _, _, _⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDg : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hg : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have h0Dg : (0 : ℂ) ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := Set.mem_insert _ _
  have hcritval := pushdown_critval_global_eq hF0 d hB hBne hsetup hBu hBl hsub hup hlo
  have hsecond : deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 := by
    intro h2
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hDg.mem_nhds h0Dg)
    obtain ⟨q₀, hq₀, a₀, ha₀, hgerm₀⟩ :=
      Work.Horn.germ_expansion_free hρ (hg.mono hball) (MandelDim.pushdown_zero d.E)
        (Work.Horn.MandelDim.deriv_pushdown_E d) h2 (pushdown_not_eventually_id d hsetup)
    obtain ⟨q, a, hq, ha, hgerm, B', hB'sub, hB'map, hB'crit, hB'disj⟩ := hspread
    have hqq : q = q₀ := germ_exponent_unique hgerm hgerm₀ ha ha₀
    exact eq_one_of_invariant_disjoint hcritval hB'sub hB'map hB'crit hB'disj (by omega)
  have hbasinCl : ∃ B' : Set ℂ,
      MandelDim.IsImmediateBasin (Work.Repel.germ1 (Work.Repel.s0 d) d.E)
        (Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl)) B' ∧
      ∃! c' : ℂ, c' ∈ B' ∧ deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) c' = 0 := by
    obtain ⟨B'', hB''im, hB''sc, zc, hzcB, hzcd⟩ := hbasind
    have hs : Work.Repel.s0 d ≠ 0 := by
      rw [Work.Repel.s0]
      exact div_ne_zero hsecond (by norm_num)
    refine ⟨(fun ζ : ℂ => Work.Repel.s0 d * ζ) '' B'', ?_, ?_⟩
    · have htrans := Work.Horn.isImmediateBasin_rescale
        (f := MandelDim.pushdown d.E) hs hB''im
      have hfun : (fun ζ : ℂ => Work.Repel.s0 d *
          MandelDim.pushdown d.E (ζ / Work.Repel.s0 d))
          = Work.Repel.germ1 (Work.Repel.s0 d) d.E := by
        funext ζ
        rw [Work.Repel.germ1_apply]
      have hdom : (fun ζ : ℂ => Work.Repel.s0 d * ζ) ''
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl))
            = Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl) := rfl
      rwa [hfun, hdom] at htrans
    · have hcrit : ∃ z ∈ (fun ζ : ℂ => Work.Repel.s0 d * ζ) '' B'',
          deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) z = 0 := by
        refine ⟨Work.Repel.s0 d * zc, ⟨zc, hzcB, rfl⟩, ?_⟩
        have hder : deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) (Work.Repel.s0 d * zc)
            = deriv (MandelDim.pushdown d.E) zc := by
          change deriv (fun w : ℂ => Work.Repel.s0 d *
            MandelDim.pushdown d.E (w / Work.Repel.s0 d)) (Work.Repel.s0 d * zc)
              = deriv (MandelDim.pushdown d.E) zc
          rw [deriv_rescale_eq (MandelDim.pushdown d.E) (Work.Repel.s0 d) hs]
          simp only [mul_div_cancel_left₀ zc hs]
        rw [hder]
        exact hzcd
      have hB'' : MandelDim.IsImmediateBasin (Work.Repel.germ1 (Work.Repel.s0 d) d.E)
          (Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl))
          ((fun ζ : ℂ => Work.Repel.s0 d * ζ) '' B'') := by
        have htrans := Work.Horn.isImmediateBasin_rescale
          (f := MandelDim.pushdown d.E) hs hB''im
        have hfun : (fun ζ : ℂ => Work.Repel.s0 d *
            MandelDim.pushdown d.E (ζ / Work.Repel.s0 d))
            = Work.Repel.germ1 (Work.Repel.s0 d) d.E := by
          funext ζ
          rw [Work.Repel.germ1_apply]
        have hdom : (fun ζ : ℂ => Work.Repel.s0 d * ζ) ''
            insert 0 (MandelDim.piExp '' (Bu ∪ Bl))
              = Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl) := rfl
        rwa [hfun, hdom] at htrans
      have hB''sc' : SimplyConnectedSpace ((fun ζ : ℂ => Work.Repel.s0 d * ζ) '' B'') :=
        Work.Horn.simplyConnectedSpace_rescale hs hB''sc
      exact existsUnique_critPoint_germ1 hF0 d hB hBne hsetup hBu hBl hsub hup hlo hsecond
        hB'' hB''sc' hcrit
  exact ⟨hsecond,
    (horn_germ_F0_of_basinClause hF0 d hB hBu hBl hsub hup hlo hsecond hbasinCl).2⟩


/-- **The target from conjunct 1 and `BasinDatum`.**  Conjunct 1 is
`Work.Horn.pushdown_second_deriv_ne_zero` and is now unconditional; the single remaining input is
`Work.Horn.BasinDatum`. -/
theorem horn_germ_F0_of_basinDatum {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hsecond : deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0)
    (hbasind : BasinDatum (d := d) (η := η) (Bu := Bu) (Bl := Bl)) :
    deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 ∧
      MandelDim.InF0
        (fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) *
          MandelDim.pushdown d.E (ζ / (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2)))
        ((fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) * ζ) ''
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
  classical
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨hBuO, hBlO, _, _, _, _, _⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDg : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hg : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have h0Dg : (0 : ℂ) ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := Set.mem_insert _ _
  have hcritval := pushdown_critval_global_eq hF0 d hB hBne hsetup hBu hBl hsub hup hlo
  have hbasinCl : ∃ B' : Set ℂ,
      MandelDim.IsImmediateBasin (Work.Repel.germ1 (Work.Repel.s0 d) d.E)
        (Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl)) B' ∧
      ∃! c' : ℂ, c' ∈ B' ∧ deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) c' = 0 := by
    obtain ⟨B'', hB''im, hB''sc, zc, hzcB, hzcd⟩ := hbasind
    have hs : Work.Repel.s0 d ≠ 0 := by
      rw [Work.Repel.s0]
      exact div_ne_zero hsecond (by norm_num)
    refine ⟨(fun ζ : ℂ => Work.Repel.s0 d * ζ) '' B'', ?_, ?_⟩
    · have htrans := Work.Horn.isImmediateBasin_rescale
        (f := MandelDim.pushdown d.E) hs hB''im
      have hfun : (fun ζ : ℂ => Work.Repel.s0 d *
          MandelDim.pushdown d.E (ζ / Work.Repel.s0 d))
          = Work.Repel.germ1 (Work.Repel.s0 d) d.E := by
        funext ζ
        rw [Work.Repel.germ1_apply]
      have hdom : (fun ζ : ℂ => Work.Repel.s0 d * ζ) ''
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl))
            = Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl) := rfl
      rwa [hfun, hdom] at htrans
    · have hcrit : ∃ z ∈ (fun ζ : ℂ => Work.Repel.s0 d * ζ) '' B'',
          deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) z = 0 := by
        refine ⟨Work.Repel.s0 d * zc, ⟨zc, hzcB, rfl⟩, ?_⟩
        have hder : deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) (Work.Repel.s0 d * zc)
            = deriv (MandelDim.pushdown d.E) zc := by
          change deriv (fun w : ℂ => Work.Repel.s0 d *
            MandelDim.pushdown d.E (w / Work.Repel.s0 d)) (Work.Repel.s0 d * zc)
              = deriv (MandelDim.pushdown d.E) zc
          rw [deriv_rescale_eq (MandelDim.pushdown d.E) (Work.Repel.s0 d) hs]
          simp only [mul_div_cancel_left₀ zc hs]
        rw [hder]
        exact hzcd
      have hB'' : MandelDim.IsImmediateBasin (Work.Repel.germ1 (Work.Repel.s0 d) d.E)
          (Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl))
          ((fun ζ : ℂ => Work.Repel.s0 d * ζ) '' B'') := by
        have htrans := Work.Horn.isImmediateBasin_rescale
          (f := MandelDim.pushdown d.E) hs hB''im
        have hfun : (fun ζ : ℂ => Work.Repel.s0 d *
            MandelDim.pushdown d.E (ζ / Work.Repel.s0 d))
            = Work.Repel.germ1 (Work.Repel.s0 d) d.E := by
          funext ζ
          rw [Work.Repel.germ1_apply]
        have hdom : (fun ζ : ℂ => Work.Repel.s0 d * ζ) ''
            insert 0 (MandelDim.piExp '' (Bu ∪ Bl))
              = Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl) := rfl
        rwa [hfun, hdom] at htrans
      have hB''sc' : SimplyConnectedSpace ((fun ζ : ℂ => Work.Repel.s0 d * ζ) '' B'') :=
        Work.Horn.simplyConnectedSpace_rescale hs hB''sc
      exact existsUnique_critPoint_germ1 hF0 d hB hBne hsetup hBu hBl hsub hup hlo hsecond
        hB'' hB''sc' hcrit
  exact ⟨hsecond,
    (horn_germ_F0_of_basinClause hF0 d hB hBu hBl hsub hup hlo hsecond hbasinCl).2⟩


theorem horn_germ_F0 (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (η : ℝ) (Bu Bl : Set ℂ)
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 ∧
      MandelDim.InF0
        (fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) *
          MandelDim.pushdown d.E (ζ / (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2)))
        ((fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) * ζ) ''
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
  have hBne : B.Nonempty := hB.2.1.nonempty
  refine horn_germ_F0_of_basinDatum hF0 d hB hBne hBu hBl hsub hup hlo ?_ ?_
  · -- CONJUNCT 1, now unconditional: `Work.Horn.pushdown_second_deriv_ne_zero`
    exact pushdown_second_deriv_ne_zero hF0 d hB hBne hBu hBl hsub hup hlo
  · -- `BasinDatum`, now derived from `MandelDim.ParabData.horn_basin` (Shishikura's horn-specific
    -- input: "`deg g₀|_{V_n}` is eventually constant / `g₀ : V_{n+1} → V_n` is a branched covering
    -- with at most one critical point"), which is a field of `ParabData` supplied by the §4.1/A.3
    -- construction.  See `Work.Horn.basinDatum_of_horn_basin`
    -- (`Submission/Work/Horn/confinement_reduction.lean`) and `NOTES_SESSION17.md` §7.
    exact basinDatum_of_horn_basin hF0 d hB hBne hBu hBl hsub hup hlo (Work.Horn.horn_basin_thm d)

end Work.Horn
