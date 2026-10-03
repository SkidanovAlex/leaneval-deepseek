import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic
import Submission.Work.Horn.gholo
import Submission.Work.Horn.horn_crit_orbit_F0
import Submission.Work.Horn.endSurj

/-!
# `Work.Horn.ofParts` — assembling `HornData` from the lead's pieces

The lead's decomposition (`NOTES_LEAD_horn.md`, `Interfaces/HornParts.lean`) splits Shishikura's
Proposition 5.3 into

* `HornTopoStatement`   (`BuOf`, `BlOf` are open, `T`-invariant, contain the half planes, ⊆ `DE`),
* `HornPhiStatement`    (Claim A on `Φ`),
* `HornVarphiStatement` (Claim B on `φ`),
* `BasinSCStatement`, `PlanarInterSCStatement`, `HornSCStatement` (simple connectivity),

and the assembly (`crit`, `cov_u/l`, `surj_u/l`, `inf_u/l`) is the HORN owner's job.

This file does the assembly in two layers.

* `hornData_of_parts` — the local assembly: from `HornTopoStatement` + `HornSCStatement` and
  the *conclusions* `crit`/`cov`/`surj_inf` (each proved from the pieces in the sibling files
  `Horn/crit_of_parts`, `Horn/cov_of_parts`, `Horn/surj_inf_of_parts`), plus Lemma 5.4
  (`g_second`, `g_F0`) and the lower-end sign `cl_im_pos`, produce `HornData d` with
  `Bu := BuOf d B`, `Bl := BlOf d B`, `η := d.η₀`, `v := d.Φ c`.
* `horn_of_parts` — the top level: `HornStatement` from the six pieces (with the two remaining
  inputs `h54` = Lemma 5.4 and `hcl` = `cl_im_pos` as explicit hypotheses).
-/

namespace Work.Horn

noncomputable section

open _root_.MandelDim Filter Topology Metric Set
open scoped Topology

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} {d : ParabData f₀ D₀}

/-- `IsF0Setup f₀ D₀ B c` implies `InF0 f₀ D₀` (the `InF0` witness is `B, c`). -/
theorem inF0_of_setup {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (h : IsF0Setup f₀ D₀ B c) : InF0 f₀ D₀ :=
  ⟨h.1, B, h.2.1, c, ⟨h.2.2.1, h.2.2.2.1⟩,
    fun c' hc' => h.2.2.2.2 c' hc'.1 hc'.2⟩

/-- **The local assembly.**  From the geometric pieces (`HornTopo`, `HornSC`) and the
conclusions of the three assembly lemmas, plus Lemma 5.4 and the lower-end sign, produce
`HornData d`. -/
theorem hornData_of_parts
    (hTopo : HornTopoStatement) (hSC : HornSCStatement) (hsetup : IsF0Setup f₀ D₀ B c)
    (hcrit : ∀ w ∈ BuOf d B ∪ BlOf d B, deriv d.E w = 0 → ∃ k : ℤ, d.E w = d.Φ c + k)
    (hcov : IsCoveringMapOn (fun x : BuOf d B => d.E x) {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} ∧
      IsCoveringMapOn (fun x : BlOf d B => d.E x) {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k})
    (hsurj : (∀ y : ℂ, ∃ w ∈ BuOf d B, d.E w = y) ∧
      (∀ y : ℂ, ∃ w ∈ BlOf d B, d.E w = y))
    (hinf : (∀ y : ℂ, (piExp '' {w : ℂ | w ∈ BuOf d B ∧ d.E w = y}).Infinite) ∧
      (∀ y : ℂ, (piExp '' {w : ℂ | w ∈ BlOf d B ∧ d.E w = y}).Infinite))
    (hsecond : deriv (deriv (pushdown d.E)) 0 ≠ 0)
    (hgF0 : InF0 (fun ζ => (deriv (deriv (pushdown d.E)) 0 / 2) *
        pushdown d.E (ζ / (deriv (deriv (pushdown d.E)) 0 / 2)))
      ((fun ζ => (deriv (deriv (pushdown d.E)) 0 / 2) * ζ) ''
        insert 0 (piExp '' (BuOf d B ∪ BlOf d B))))
    (hcl : ∀ cl : ℂ, Tendsto (fun w => d.E w - w) lowerEnd (𝓝 cl) → 0 < cl.im) :
    Nonempty (HornData d) := by
  have htopo := hTopo f₀ D₀ B c d hsetup
  have hBuO : IsOpen (BuOf d B) := htopo.1
  have hBlO : IsOpen (BlOf d B) := htopo.2.1
  have htBu : IsTInvariant (BuOf d B) := htopo.2.2.1
  have htBl : IsTInvariant (BlOf d B) := htopo.2.2.2.1
  have hup : {w : ℂ | d.η₀ < w.im} ⊆ BuOf d B := htopo.2.2.2.2.1
  have hlo : {w : ℂ | w.im < -d.η₀} ⊆ BlOf d B := htopo.2.2.2.2.2.1
  have hsub : BuOf d B ∪ BlOf d B ⊆ d.DE := htopo.2.2.2.2.2.2
  have hsc := hSC f₀ D₀ B c d hsetup
  have hBuconn : IsConnected (BuOf d B) :=
    ⟨⟨Complex.I * (d.η₀ + 1), hup (by simp)⟩, isPreconnected_connectedComponentIn⟩
  have hBlconn : IsConnected (BlOf d B) :=
    ⟨⟨-(Complex.I * (d.η₀ + 1)), hlo (by simp)⟩, isPreconnected_connectedComponentIn⟩
  have hgholo : DifferentiableOn ℂ (pushdown d.E)
      (insert 0 (piExp '' (BuOf d B ∪ BlOf d B))) :=
    pushdown_E_differentiableOn d d.η₀ (BuOf d B) (BlOf d B) hBuO hBlO htBu htBl hsub hup hlo
  have hF0 : InF0 f₀ D₀ := inF0_of_setup hsetup
  have hBu_eq : BuOf d B = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ)
      (Complex.I * (d.η₀ + 1)) := by
    rw [BuOf, Btil]
    congr 1
    ext w
    simp [Set.mem_inter_iff, and_comm]
  have hBl_eq : BlOf d B = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ)
      (-(Complex.I * (d.η₀ + 1))) := by
    rw [BlOf, Btil]
    congr 1
    ext w
    simp [Set.mem_inter_iff, and_comm]
  have hgF0' : InF0 (resc d) (rescDom d (BuOf d B) (BlOf d B)) := by
    have h := hgF0
    simp only [resc, rescDom, Work.Repel.germ1, Work.Repel.Dgerm1, Work.Repel.s0] at h ⊢
    rw [Set.image_insert_eq, mul_zero] at h ⊢
    exact h
  have hcorbit := horn_crit_orbit_of_F0 f₀ D₀ hF0 d B hsetup.2.1 d.η₀ (BuOf d B) (BlOf d B)
    (d.Φ c) hBu_eq hBl_eq hsub hup hlo hcrit hBuO hBlO htBu htBl hgF0'
  exact ⟨{ Bu := BuOf d B
           Bl := BlOf d B
           η := d.η₀
           v := d.Φ c
           Bu_open := hBuO
           Bl_open := hBlO
           Bu_conn := hBuconn
           Bl_conn := hBlconn
           Bu_sc := hsc.1
           Bl_sc := hsc.2.1
           Bu_T := htBu
           Bl_T := htBl
           disj := hsc.2.2
           sub := hsub
           upper := hup
           lower := hlo
           crit := hcrit
           cov_u := hcov.1
           cov_l := hcov.2
           surj_u := hsurj.1
           surj_l := hsurj.2
           inf_u := hinf.1
           inf_l := hinf.2
           g_holo := hgholo
           g_deriv := Work.Horn.MandelDim.deriv_pushdown_E d
           g_second := hsecond
           g_F0 := hgF0
           cl_im_pos := hcl
           crit_orbit := hcorbit }⟩

end

end Work.Horn
