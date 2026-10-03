import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec
import Submission.Work.Horn.basin
import Submission.Work.Horn.basin_rescale
import Submission.Work.Horn.locally_open_of_not_locally_const
import Submission.Work.Horn.gholo
import Submission.Work.Horn.pushdown_not_locally_const
import Submission.Work.L62.basin_iface
import Submission.Work.Parab.basinCoord.exists_basin_coordinate
import Submission.Work.Parab.basinEnters.zero_not_mem_basin
import Submission.Work.Repel.hornE_not_locally_const
import Submission.Work.Repel.orbit_ne_zero_of_nowhere_locally_const

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-!
# The orbit of a basin point of the level-1 base germ `ǧ₀ = g0germ d` never hits `0`

`g0germ d = germ1 (s0 d) d.E` is the rescaled pushdown of the unperturbed horn map `d.E = Φ ∘ φ`
of the §4.1 data of `f₀`; it is the parabolic germ of the second level of Shishikura §6.  The
statement proved here,

`∀ z ∈ ParabolicBasin (g0germ d) (Dg0germ d hd), ∀ n, (g0germ d)^[n] z ≠ 0`,

is the non-degeneracy hypothesis of `MandelDim.ParabStatement` at level 1 (used by the §6 assembly
to apply Lemma 5.1 / PARAB0 to `ǧ₀`).

The proof does **not** use the §4.1 petal machinery (which would be circular: the petal-based
forward invariance of the basin, `Work.L62.parabolicBasin_forward`, consumes exactly this
non-degeneracy statement).  Instead:

* the basin of a parabolic germ is forward invariant as soon as the germ is locally open at the
  basin points (`Work.Horn.MandelDim.basin_basic`), and local openness holds at every point where
  the germ is not locally constant (`Work.Horn.locally_open_of_not_locally_const`);
* `0` is never in the basin (`Work.Parab.basinEnters.zero_not_mem_parabolicBasin`);
* so it remains to see that `g0germ d` is nowhere locally constant on its domain, which we reduce
  to the horn map: `d.E` is nowhere locally constant on `Bu ∪ Bl` (child lemma
  `hornE_not_locally_const`), and local constancy transfers both through the covering `π`
  (`Work.Horn.pushdown_not_locally_const`) and through the rescaling `ζ ↦ s0 d * ζ`
  (`germ1_eventuallyEq_const_iff`).
-/

/-! ## Local constancy transfers through the rescaling `ζ ↦ s * ζ` -/

/-- `germ1 s R` is the conjugate of `pushdown R` by the dilation `ζ ↦ s * ζ`; consequently local
constancy at `s * u` for `germ1 s R` is the same as local constancy at `u` for `pushdown R`
(`s ≠ 0`). -/
theorem germ1_eventuallyEq_const_iff {s : ℂ} (hs : s ≠ 0) (R : ℂ → ℂ) (u : ℂ) :
    (∀ᶠ ζ in nhds (s * u), germ1 s R ζ = germ1 s R (s * u)) ↔
      (∀ᶠ v in nhds u, pushdown R v = pushdown R u) := by
  have hsu : germ1 s R (s * u) = s * pushdown R u := by
    rw [germ1_apply, mul_div_cancel_left₀ u hs]
  constructor
  · intro h
    have ht : Tendsto (fun v : ℂ => s * v) (nhds u) (nhds (s * u)) :=
      (continuous_const.mul continuous_id).tendsto u
    filter_upwards [ht.eventually h] with v hv
    rw [germ1_apply, mul_div_cancel_left₀ v hs, hsu] at hv
    exact mul_left_cancel₀ hs hv
  · intro h
    have ht : Tendsto (fun ζ : ℂ => ζ / s) (nhds (s * u)) (nhds u) := by
      have hcont : Continuous fun ζ : ℂ => ζ / s := continuous_id.div_const s
      have h := hcont.tendsto (s * u)
      rwa [mul_div_cancel_left₀ u hs] at h
    filter_upwards [ht.eventually h] with ζ hζ
    rw [germ1_apply, germ1_apply, mul_div_cancel_left₀ u hs, hζ]

/-! ## The horn map as a map on a `T`-invariant piece of `d.DE` -/

/-- `d.DE = d.Dφ ∩ φ⁻¹(basin)` is open. -/
lemma isOpen_DE {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) : IsOpen d.DE := by
  rw [show d.DE = d.Dφ ∩ d.φ ⁻¹' MandelDim.ParabolicBasin f₀ D₀ from rfl]
  exact d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open
    (Work.L62.isOpen_parabolicBasin f₀ D₀)

/-- `E = Φ ∘ φ` is `T`-equivariant at every point of `d.DE`. -/
lemma E_add_one_of_mem {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {u : ℂ}
    (hu : u ∈ d.DE) : d.E (u + 1) = d.E u + 1 := by
  have hφD : d.φ u ∈ D₀ := Work.L62.parabolicBasin_subset f₀ D₀ hu.2
  have hsucc : u + 1 ∈ d.Dφ := (d.succ_iff u hu.1).mpr hφD
  change d.Φ (d.φ (u + 1)) = d.Φ (d.φ u) + 1
  rw [d.φ_abel u hu.1 hsucc]
  exact d.Φ_abel (d.φ u) hu.2

/-- `d.E` is continuous at every point of `d.DE`. -/
lemma continuousAt_E_of_mem {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {w : ℂ}
    (hw : w ∈ d.DE) : ContinuousAt d.E w :=
  ((Work.Horn.differentiableOn_E d).differentiableAt ((isOpen_DE d).mem_nhds hw)).continuousAt

/-- **Descending local non-constancy of the horn map through `π`.**  If `d.E` is nowhere locally
constant on a `T`-invariant open `S ⊆ d.DE`, then `pushdown d.E` is nowhere locally constant on
`π '' S`. -/
lemma pushdown_not_locally_const_of_mem {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {S : Set ℂ} (hSo : IsOpen S) (hST : MandelDim.IsTInvariant S) (hsubS : S ⊆ d.DE)
    (hnlc : ∀ w ∈ S, ¬ (∀ᶠ u in nhds w, d.E u = d.E w)) {w : ℂ} (hw : w ∈ S) :
    ¬ (∀ᶠ ζ in nhds (MandelDim.piExp w),
        MandelDim.pushdown d.E ζ = MandelDim.pushdown d.E (MandelDim.piExp w)) :=
  Work.Horn.pushdown_not_locally_const hST (fun u hu _ => E_add_one_of_mem d (hsubS hu)) hw
    (hSo.mem_nhds hw) (continuousAt_E_of_mem d (hsubS hw)) (hnlc w hw)

/-! ## The level-1 base germ is nowhere locally constant -/

/-- **`ǧ₀ = g0germ d` is nowhere locally constant on its domain.**  For `ζ = s0 · π w` (`w` in one
of the two horns) this descends to the horn map (`pushdown_not_locally_const_of_mem` +
`germ1_eventuallyEq_const_iff`); at `ζ = 0` it is the derivative `(g0germ d)'(0) = 1 ≠ 0`. -/
lemma g0germ_not_locally_const {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.HornData d) :
    ∀ ζ ∈ Dg0germ d hd, ¬ (∀ᶠ z in nhds ζ, g0germ d z = g0germ d ζ) := by
  have hs : s0 d ≠ 0 := s0_ne_zero d hd
  have hg : MandelDim.IsParabolicGerm (g0germ d) (Dg0germ d hd) := isParabolicGerm_g0germ d hd
  intro ζ hζ hconst
  rw [Dg0germ_eq d hd] at hζ
  obtain ⟨u, hu, rfl⟩ := hζ
  rcases Set.mem_insert_iff.mp hu with rfl | hu
  · -- `u = 0`: `(g0germ d)'(0) = 1` forbids local constancy at `0`
    simp only [mul_zero] at hconst
    have hder := Filter.EventuallyEq.deriv_eq hconst
    rw [hg.2.2.2.2.1] at hder
    simpa using hder
  · -- `u = π w` with `w` in one of the two horns
    obtain ⟨w, hw, rfl⟩ := hu
    have hpu : ¬ (∀ᶠ v in nhds (MandelDim.piExp w),
        MandelDim.pushdown d.E v = MandelDim.pushdown d.E (MandelDim.piExp w)) := by
      rcases hw with hwBu | hwBl
      · exact pushdown_not_locally_const_of_mem d hd.Bu_open hd.Bu_T
          (fun u hu => hd.sub (Or.inl hu))
          (fun w hw => hornE_not_locally_const d hd w (Or.inl hw)) hwBu
      · exact pushdown_not_locally_const_of_mem d hd.Bl_open hd.Bl_T
          (fun u hu => hd.sub (Or.inr hu))
          (fun w hw => hornE_not_locally_const d hd w (Or.inr hw)) hwBl
    exact hpu ((germ1_eventuallyEq_const_iff hs d.E (MandelDim.piExp w)).mp hconst)

/-! ## The target -/

theorem orbit_ne_zero_g0germ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.HornData d) :
    ∀ z ∈ MandelDim.ParabolicBasin (Work.Repel.g0germ d) (Work.Repel.Dg0germ d hd),
      ∀ n : ℕ, ((Work.Repel.g0germ d)^[n]) z ≠ 0 :=
  orbit_ne_zero_of_nowhere_locally_const (isParabolicGerm_g0germ d hd)
    (g0germ_not_locally_const d hd)

end

end Work.Repel
