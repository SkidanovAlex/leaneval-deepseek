import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Repel.Spec
import Submission.Work.Horn.basin_rescale
import Submission.Work.Horn.deriv_pushdown_zero

/-!
# HORN: the critical orbit of the pushed-down horn map, given the `𝓕₀`-structure

The requested lemma `Work.Horn.horn_crit_orbit` asks for the conclusion
`(∀ n, g^[n] (π v) ∈ π '' (Bu ∪ Bl)) ∧ Tendsto (fun n => g^[n] (π v)) atTop (𝓝 0)`
(`g = pushdown d.E`) from `ParabData` + `IsImmediateBasin` + `hsub`/`hup`/`hlo` + the
critical-value hypothesis `hcrit` alone.  That is *not* provable: `hcrit` only *constrains* `v`
when `E` has a critical point in `Bu ∪ Bl` (whose existence is Shishikura's Prop. 5.3, not a
`ParabData` field), and it says nothing about the dynamics of `g`; the convergence clause is
exactly Lemma 5.4's hard content, `π v` being the critical value of `g` lying in its immediate
parabolic basin.

This file proves the statement in the form in which it *is* provable and in which the assembly
uses it: with the extra hypothesis that the rescaled pushed-down horn map lies in `𝓕₀`
(Shishikura's Lemma 5.4, first half — the `HornData.g_F0` field, proved by
`Work.Horn.horn_germ_F0`), plus the `ℤ`-invariance of `d.DE` (a structural fact of the §4.1 data,
`Work.L62.basin_iface`).  From `InF0` of the rescaled germ we get its immediate parabolic basin
and the uniqueness of its critical point; `hcrit` identifies the critical value with `π v`;
forward invariance of the basin puts `π v` in the basin, which gives both the membership clause
and the convergence.
-/

open MandelDim Set Filter Topology Metric
open scoped Topology

namespace Work.Horn

noncomputable section

/-- The pushed-down horn map `g = pushdown Ẽ`. -/
abbrev g {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) : ℂ → ℂ := pushdown d.E

/-- The map whose `𝓕₀`-structure is needed: the rescaled pushed-down horn map
`s * g(· / s)`, `s = g''(0)/2`. -/
abbrev resc {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) : ℂ → ℂ :=
  Work.Repel.germ1 (Work.Repel.s0 d) d.E

theorem resc_eq {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    resc d = fun ζ => Work.Repel.s0 d * g d (ζ / Work.Repel.s0 d) := rfl

/-- Its domain: the `s`-image of `{0} ∪ π(Bu ∪ Bl)`. -/
abbrev rescDom {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (Bu Bl : Set ℂ) : Set ℂ :=
  Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl)

theorem rescDom_eq {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (Bu Bl : Set ℂ) :
    rescDom d Bu Bl = (fun ζ => Work.Repel.s0 d * ζ) '' (insert 0 (piExp '' (Bu ∪ Bl))) :=
  rfl

/-- `π` never vanishes. -/
theorem piExp_ne_zero' (w : ℂ) : piExp w ≠ 0 := Complex.exp_ne_zero _

/-- `pushdown E` never vanishes away from `0`. -/
theorem pushdown_ne_zero_of_ne {E : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ≠ 0) : pushdown E ζ ≠ 0 := by
  rw [MandelDim.pushdown_of_ne E hζ]
  exact piExp_ne_zero' _

/-- `germ1 s R (s * z) = s * pushdown R z` (compare `Work.Repel.germ1_apply`). -/
theorem germ1_mul (s : ℂ) (R : ℂ → ℂ) (z : ℂ) :
    Work.Repel.germ1 s R (s * z) = s * pushdown R z := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Work.Repel.germ1]
  · rw [Work.Repel.germ1_apply, mul_div_cancel_left₀ z hs]

/-- Iterating `germ1_mul`: `(germ1 s R)^[n] (s * z) = s * (pushdown R)^[n] z`. -/
theorem germ1_iterate (s : ℂ) (R : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    (Work.Repel.germ1 s R)^[n] (s * z) = s * (pushdown R)^[n] z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', germ1_mul]

/-- The parabolic basin is open (from the definition). -/
theorem isOpen_basin (f : ℂ → ℂ) (D : Set ℂ) : IsOpen (ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hmap, hunif⟩
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  refine mem_of_superset (hVopen.mem_nhds hzV) fun y hy =>
    ⟨V, hVopen.mem_nhds hy, fun n => (hmap n).mono hVU Subset.rfl, hunif.mono hVU⟩

/-- The basin is contained in the domain. -/
theorem basin_subset (f : ℂ → ℂ) (D : Set ℂ) : ParabolicBasin f D ⊆ D := by
  rintro z ⟨U, hU, hmap, -⟩
  exact hmap 0 (mem_of_mem_nhds hU)

/-- `E = Φ ∘ φ` is holomorphic on its domain `DE`. -/
theorem E_diffOn_DE {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    DifferentiableOn ℂ d.E d.DE := by
  intro w hw
  have hmap : MapsTo d.φ d.DE (ParabolicBasin f₀ D₀) := fun x hx => hx.2
  have hφ : DifferentiableWithinAt ℂ d.φ d.DE w := (d.φ_holo w hw.1).mono (fun x hx => hx.1)
  have hΦ : DifferentiableWithinAt ℂ d.Φ (ParabolicBasin f₀ D₀) (d.φ w) := d.Φ_holo (d.φ w) hw.2
  exact hΦ.comp w hφ hmap

/-- `d.DE` is open. -/
theorem isOpen_DE {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    IsOpen d.DE := by
  have hb : IsOpen (ParabolicBasin f₀ D₀) := isOpen_basin f₀ D₀
  exact d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open hb

/-- Derivative of the rescaled map. -/
theorem deriv_resc {s : ℂ} (hs : s ≠ 0) {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    deriv (fun ζ => s * f (ζ / s)) (s * z) = deriv f z := by
  have h1 : DifferentiableAt ℂ (fun ζ : ℂ => ζ / s) (s * z) := differentiableAt_id.div_const s
  have hf' : DifferentiableAt ℂ f (s * z / s) := by
    simpa [mul_div_cancel_left₀ z hs] using hf
  have h2 : DifferentiableAt ℂ (fun ζ : ℂ => f (ζ / s)) (s * z) := hf'.comp (s * z) h1
  rw [deriv_const_mul _ h2]
  have h3 : deriv (fun ζ : ℂ => f (ζ / s)) (s * z) =
      deriv f ((s * z) / s) * deriv (fun ζ : ℂ => ζ / s) (s * z) :=
    deriv_comp (x := s * z) (h := fun ζ : ℂ => ζ / s) (h₂ := f) hf' h1
  rw [h3, mul_div_cancel_left₀ z hs, deriv_div_const, deriv_id'']
  field_simp

/-- Differentiability is preserved by the rescaling. -/
theorem differentiableAt_resc {s : ℂ} (hs : s ≠ 0) {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℂ (fun ζ => s * f (ζ / s)) (s * z) ↔ DifferentiableAt ℂ f z := by
  constructor
  · intro h
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => f (ζ / s)) (s * z) := by
      have h2 : DifferentiableAt ℂ (fun ζ : ℂ => s⁻¹ * (s * f (ζ / s))) (s * z) := h.const_mul s⁻¹
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards with ζ
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    have h3 : DifferentiableAt ℂ (fun ζ : ℂ => s * ζ) z := by
      simpa using differentiableAt_id.const_mul s
    have h4 := h1.comp z h3
    have h5 : ((fun ζ : ℂ => f (ζ / s)) ∘ (fun ζ : ℂ => s * ζ)) = f := by
      funext y; simp [mul_div_cancel_left₀ y hs]
    rw [h5] at h4
    exact h4
  · intro h
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => ζ / s) (s * z) := differentiableAt_id.div_const s
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => f (ζ / s)) (s * z) := by
      have h3 : DifferentiableAt ℂ f ((fun ζ : ℂ => ζ / s) (s * z)) := by
        simpa [mul_div_cancel_left₀ z hs] using h
      exact h3.comp (s * z) h1
    exact h2.const_mul s

/-- **The exact missing hypothesis.**  If the critical value `π v` of the pushed-down horn map
already lies in its parabolic basin, then the critical-orbit conclusion holds: all iterates stay
in the domain `{0} ∪ π(Bu ∪ Bl)` (they avoid `0` because `pushdown E` never vanishes away from
`0`) and converge to `0` (from the locally uniform convergence defining the basin). -/
theorem crit_orbit_of_mem_basin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀)
    {Bu Bl : Set ℂ} {v : ℂ}
    (hbasin : piExp v ∈ ParabolicBasin (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl)))) :
    (∀ n : ℕ, (pushdown d.E)^[n] (piExp v) ∈ piExp '' (Bu ∪ Bl)) ∧
      Filter.Tendsto (fun n : ℕ => (pushdown d.E)^[n] (piExp v)) Filter.atTop (nhds 0) := by
  obtain ⟨U, hU, hmapU, hunifU⟩ := hbasin
  obtain ⟨V, hVU, hVopen, hπvV⟩ := _root_.mem_nhds_iff.mp hU
  have hmapV : ∀ n : ℕ, MapsTo ((pushdown d.E)^[n]) V (insert 0 (piExp '' (Bu ∪ Bl))) :=
    fun n => (hmapU n).mono hVU Subset.rfl
  have hconv : Filter.Tendsto (fun n : ℕ => (pushdown d.E)^[n] (piExp v)) Filter.atTop (nhds 0) :=
    (hunifU.mono hVU).tendsto_at hπvV
  refine ⟨fun n => ?_, hconv⟩
  have h2 : (pushdown d.E)^[n] (piExp v) ≠ 0 := by
    induction n with
    | zero => simpa using piExp_ne_zero' v
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact pushdown_ne_zero_of_ne ih
  have h1 : (pushdown d.E)^[n] (piExp v) ∈ insert 0 (piExp '' (Bu ∪ Bl)) := hmapV n hπvV
  rcases Set.mem_insert_iff.mp h1 with h | h
  · exact absurd h h2
  · exact h

/-- **The critical orbit of the pushed-down horn map, given the `𝓕₀`-structure of the
rescaled map.**  This is the requested statement `Work.Horn.horn_crit_orbit` with the extra
hypotheses `hBuT`/`hBlT` (two-sided `ℤ`-invariance of the two components, from
`HornTopoStatement`) and `hg`
(`InF0` of the rescaled pushed-down map, i.e. Shishikura's Lemma 5.4 / the `HornData.g_F0`
field).  Both are available in the assembly. -/
theorem horn_crit_orbit_of_F0 (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (η : ℝ) (Bu Bl : Set ℂ) (v : ℂ)
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hcrit : ∀ w ∈ Bu ∪ Bl, deriv d.E w = 0 → ∃ k : ℤ, d.E w = v + k)
    (hBuO : IsOpen Bu) (hBlO : IsOpen Bl)
    (hBuT : MandelDim.IsTInvariant Bu) (hBlT : MandelDim.IsTInvariant Bl)
    (hg : MandelDim.InF0 (resc d) (rescDom d Bu Bl)) :
    (∀ n : ℕ, (MandelDim.pushdown d.E)^[n] (MandelDim.piExp v) ∈ MandelDim.piExp '' (Bu ∪ Bl)) ∧
      Filter.Tendsto (fun n : ℕ => (MandelDim.pushdown d.E)^[n] (MandelDim.piExp v))
        Filter.atTop (nhds 0) := by
  classical
  set s : ℂ := Work.Repel.s0 d with hsdef
  set Dg : Set ℂ := insert 0 (piExp '' (Bu ∪ Bl)) with hDgdef
  have hresc : resc d = fun ζ => s * g d (ζ / s) := by rw [hsdef]; rfl
  have hDhat_eq : rescDom d Bu Bl = (fun ζ => s * ζ) '' Dg := by rw [hsdef, hDgdef]; rfl
  obtain ⟨hge, Bh, hBh, ch, hch, huniqch⟩ := hg
  -- `s ≠ 0`
  have hs : s ≠ 0 := by
    intro hs0
    have hs0' : Work.Repel.s0 d = 0 := by rw [← hsdef]; exact hs0
    have h := hge.2.2.2.2.1
    have hzero : resc d = fun _ : ℂ => (0 : ℂ) := by
      funext ζ
      simp [resc, Work.Repel.germ1, hs0', MandelDim.pushdown_zero]
    rw [hzero] at h
    simpa using h
  have hEeq : ∀ w ∈ d.DE, w + 1 ∈ d.DE → d.E (w + 1) = d.E w + 1 :=
    fun w hw hw1 => MandelDim.ParabData.E_add_one d hw hw1
  have heqBu : ∀ u ∈ Bu, d.E (u + 1) = d.E u + 1 := fun u hu =>
    hEeq u (hsub (Or.inl hu)) (hsub (Or.inl ((hBuT u).mp hu)))
  have heqBl : ∀ u ∈ Bl, d.E (u + 1) = d.E u + 1 := fun u hu =>
    hEeq u (hsub (Or.inr hu)) (hsub (Or.inr ((hBlT u).mp hu)))
  have hDEopen : IsOpen d.DE := isOpen_DE d
  -- the critical point of the rescaled germ, transported back
  have hchmem : ch ∈ rescDom d Bu Bl := basin_subset _ _ (hBh.2.2.1 hch.1)
  have hchdiff : DifferentiableAt ℂ (resc d) ch :=
    (hge.2.2.1 ch hchmem).differentiableAt (hge.1.mem_nhds hchmem)
  set c : ℂ := ch / s with hcdef
  have hsc : s * c = ch := by rw [hcdef]; exact mul_div_cancel₀ ch hs
  have hgdiff : DifferentiableAt ℂ (g d) c := by
    have h1 : DifferentiableAt ℂ (resc d) (s * c) := by rw [hsc]; exact hchdiff
    rw [hresc] at h1
    exact (differentiableAt_resc (s := s) (f := g d) (z := c) hs).mp h1
  have hderivc : deriv (g d) c = 0 := by
    have h1 : deriv (fun ζ => s * g d (ζ / s)) (s * c) = deriv (g d) c :=
      deriv_resc (f := g d) (s := s) hs hgdiff
    rw [← h1, ← hresc, hsc]
    exact hch.2
  have hg0 : deriv (g d) 0 = 1 := by
    have hch0 : DifferentiableAt ℂ (resc d) 0 :=
      (hge.2.2.1 0 hge.2.1).differentiableAt (hge.1.mem_nhds hge.2.1)
    rw [hresc] at hch0
    have h0 : DifferentiableAt ℂ (g d) 0 :=
      (differentiableAt_resc (s := s) (f := g d) (z := 0) hs).mp (by simpa using hch0)
    have h1 : deriv (resc d) 0 = deriv (g d) 0 := by
      rw [hresc]
      simpa using deriv_resc (f := g d) (s := s) hs (z := 0) h0
    rw [← h1]
    exact hge.2.2.2.2.1
  have hcne : c ≠ 0 := by
    intro hc0
    have h := hderivc
    rw [hc0, hg0] at h
    exact one_ne_zero h
  have hcDg : c ∈ Dg := by
    have hc : ch ∈ (fun ζ => s * ζ) '' Dg := by rw [← hDhat_eq]; exact hchmem
    obtain ⟨z, hz, hzc⟩ := hc
    have hcz : c = z := by rw [hcdef, ← hzc, mul_div_cancel_left₀ z hs]
    rwa [hcz]
  have hcπ : c ∈ piExp '' (Bu ∪ Bl) := by
    have h := hcDg
    rw [hDgdef] at h
    rcases Set.mem_insert_iff.mp h with h | h
    · exact absurd h hcne
    · exact h
  obtain ⟨w, hwBuBl, hwpi⟩ := hcπ
  have hwDE : w ∈ d.DE := hsub hwBuBl
  have hEdiff : DifferentiableAt ℂ d.E w :=
    (E_diffOn_DE d w hwDE).differentiableAt (hDEopen.mem_nhds hwDE)
  have hEcrit : deriv d.E w = 0 := by
    have hd : DifferentiableAt ℂ (MandelDim.pushdown d.E) (piExp w) := by
      rw [hwpi]; exact hgdiff
    have hderivc' : deriv (MandelDim.pushdown d.E) (piExp w) = 0 := by rw [hwpi]; exact hderivc
    rcases hwBuBl with hwB | hwB
    · exact (deriv_pushdown_zero hBuT hwB (hBuO.mem_nhds hwB) heqBu hEdiff hd).mp hderivc'
    · exact (deriv_pushdown_zero hBlT hwB (hBlO.mem_nhds hwB) heqBl hEdiff hd).mp hderivc'
  obtain ⟨k, hk⟩ := hcrit w hwBuBl hEcrit
  have hv : piExp v = g d c := by
    rw [← hwpi]
    show piExp v = MandelDim.pushdown d.E (piExp w)
    rcases hwBuBl with hwB | hwB
    · rw [MandelDim.pushdown_piExp hBuT (fun u hu _ => heqBu u hu) hwB, hk,
        MandelDim.piExp_add_intCast]
    · rw [MandelDim.pushdown_piExp hBlT (fun u hu _ => heqBl u hu) hwB, hk,
        MandelDim.piExp_add_intCast]
  -- the basin of the rescaled map transports to the basin of `g`
  have hs_gc_Bh : s * g d c ∈ Bh := by
    have h1 : resc d (s * c) = s * g d c := by
      show Work.Repel.germ1 s d.E (s * c) = s * g d c
      exact germ1_mul s d.E c
    have h2 : resc d (s * c) ∈ Bh := by rw [hsc]; exact hBh.2.2.2.2.1 hch.1
    rwa [h1] at h2
  have hgc_basin : g d c ∈ ParabolicBasin (MandelDim.pushdown d.E) Dg :=
    (basin_rescale (R := d.E) (D := Dg) hs (g d c)).mpr (by
      rw [← hDhat_eq]
      exact hBh.2.2.1 hs_gc_Bh)
  obtain ⟨U, hU, hmapU, hunifU⟩ := hgc_basin
  obtain ⟨V, hVU, hVopen, hgcV⟩ := _root_.mem_nhds_iff.mp hU
  have hunifV : TendstoUniformlyOn (fun n : ℕ => (g d)^[n]) 0 Filter.atTop V := hunifU.mono hVU
  have hconv : Filter.Tendsto (fun n : ℕ => (g d)^[n] (g d c)) Filter.atTop (nhds 0) :=
    hunifV.tendsto_at hgcV
  have hmem : ∀ n : ℕ, (g d)^[n] (g d c) ∈ piExp '' (Bu ∪ Bl) := by
    intro n
    have h2 : (g d)^[n] (g d c) ≠ 0 := by
      induction n with
      | zero => rw [Function.iterate_zero_apply, hv.symm]; exact piExp_ne_zero' v
      | succ m ih =>
          rw [Function.iterate_succ_apply']
          exact pushdown_ne_zero_of_ne ih
    have hmapV : ∀ k : ℕ, MapsTo ((g d)^[k]) V Dg := fun k => (hmapU k).mono hVU Subset.rfl
    have h1 : (g d)^[n] (g d c) ∈ Dg := hmapV n hgcV
    rw [hDgdef] at h1
    rcases Set.mem_insert_iff.mp h1 with h | h
    · exact absurd h h2
    · exact h
  refine ⟨fun n => ?_, ?_⟩
  · rw [hv]
    exact hmem n
  · rw [show (fun n : ℕ => (MandelDim.pushdown d.E)^[n] (MandelDim.piExp v)) =
        fun n : ℕ => (g d)^[n] (g d c) from by funext n; rw [hv]]
    exact hconv

end

end Work.Horn
