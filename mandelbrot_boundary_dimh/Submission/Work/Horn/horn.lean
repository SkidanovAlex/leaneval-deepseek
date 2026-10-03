import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.assembly
import Submission.Work.Horn.hornOfParts
import Submission.Work.Horn.horn_germ_F0
import Submission.Work.Horn.hcl_of_parts
import Submission.Work.HornTopo.horn_topo
import Submission.Work.HornSC.horn_sc
import Submission.Work.HornPhi.horn_phi
import Submission.Work.HornVarphi.horn_varphi
import Submission.Work.BasinSC.basin_sc
import Submission.Work.PlanarSC.planar_inter_sc

/-! Guidance from the project lead (the requester):

AREA HORN: prove HornStatement (Prop 5.3 lifted + Lemma 5.4 for the class F0, giving HornData). Applied to f0 and to the rescaled horn map. Mathlib covering-space API: IsCoveringMapOn, IsCoveringMapOn.existsUnique_continuousMap_lifts. Planar topology is the risk: if you need the Jordan curve theorem, tell the lead (a sorry-free Jordan/Schoenflies closure exists in the fleet and can be copied in).
Contracts: Submission/Work/Interfaces/Parabolic.lean (namespace MandelDim; imports Interfaces/Basic.lean and Interfaces/Fatou.lean). Blueprint: NOTES_LEAD_parabolic.md and NOTES_LEAD_fatou.md at the workspace root (cat them). Paper: REFS/shishikura_math9201282/hdim4.tex, hdim5.tex, hdim6.tex, hdimB.tex. Every area may ASSUME the other areas' Props (it takes them as hypotheses where its statement says so); never weaken or edit the interface files. If a field of a contract structure is false or unprovable as stated, report it with a counterexample and the exact corrected field (the contracts are a first design; refereeing them early is valuable). Go wide: request all independent sub-lemmas at once.

### Lemma 5.4 inside HORN — how to get `q = 1` cheaply
The paper invokes Lemma 5.2 for general `q`. Needed instead:
- (a) The flower for multiplicity `q+1` (petals only, no Fatou coordinates). Use the coordinate
  `w = -1/(q a z^q)` on sectors, where `w ↦ w + 1 + O(|w|^{-1/q})`: 4–6K.
- (b) Each petal lies in a different immediate basin. The petal an orbit enters is locally
  constant on a connected basin.
- (c) Each immediate basin `B_i ⊆ B^u` is **bounded**. If `B_i` had no critical point, the
  Fatou coordinate would make `B_i ≅ ℂ`, contradicting Liouville.
- (d) So each `B_i` contains a critical point, and its value is the unique critical value
  `π v`. Invariance puts `π v` in every `B_i`, which forces `q = 1`.

"Exactly one critical point in the immediate basin" is the `V_n` chain: proper maps between
simply connected domains with one branch value. Use the uniformization library's Riemann map, or
cyclic coverings of the punctured domain.


## 1. Formalism decisions

1. **Functions with domains → explicit closeness.** We never build Shishikura's §4.0 topology.
   - A neighbourhood of `f₀` is a pair `(L compact ⊆ D₀, δ₀)`. The statement is
     `NearOn f₀ f Df L δ₀`: `f` is holomorphic on an open `Df ⊇ L` and `δ₀`-close to `f₀` on `L`.
   - Every "as `f → f₀`" statement becomes `∀ targets (K, K', y₁, δ), ∃ (L, δ₀), ∀ f, NearOn … →`.
2. **Horn maps and return maps are handled only in LIFTED form.**
   - A horn map or return map is a `T`-equivariant map on a `T`-invariant open subset of `ℂ`
     (`IsTEquivariantOn`).
   - The cylinder ends are `upperEnd`/`lowerEnd` (the `comap im`), and both ends are handled
     uniformly. This is how the level-2 map `h₀` is used at `0` and at `∞`.
   - The pushed-down germ at `0` is `pushdown E`. It is used only where a map on `ℂ` is needed:
     `g₀` as a level-1 germ, and Lemma 6.1.
3. **Existential objects are passed as data structures.**
   - `ParabData f₀ D₀`, `PertData d f Df η y₁ K K' δ` and `HornData d` are structures holding data
     plus properties. Producers prove `Nonempty (...)`; consumers `obtain ⟨d⟩`.
   - `ParabData` pins `(φ₀, Φ₀)` up to one common translation. It does this with the Abel
     equations, injectivity on the petals, the asymptotics, and the normalisation
     `E w - w → 0` at the upper end. So PERT's convergence "to `d.φ`, `d.E`" is meaningful for
     *any* `d`.
4. **Germ class.** The class is `IsParabolicGerm f D`: `f z = z + z² + O(z³)` on an open `D ∋ 0`.
   - `𝓕₀` is `InF0`: an immediate basin (a component of the basin, invariant, proper) with
     exactly one critical point.
   - `g₀` has `g₀''(0) ≠ 0` but not necessarily `= 2`. The assembly conjugates by `ζ ↦ sζ`,
     `s = g₀''(0)/2`, and `HornData.g_F0` is stated for the rescaled map. Everything else is
     invariant under the rescaling (`α`, closeness up to the factor `s`).
5. **Branch conventions.**
   - `alphaOf f = log f'(0)/(2πi)` uses the principal log, so `-1/2 < Re α ≤ 1/2`.
   - `InF1 α := |Im α| < Re α` (Shishikura's `𝓕₁`).
   - Level 0 has `α = 1/(a₁ - 1/(a₂+β))`. Level 1 has `alphaOf g = 1/(a₂+β)` *exactly*: from
     `R_upper` we get `g'(0) = e^{-2πi/α}`, and `-1/α ≡ 1/(a₂+β) mod ℤ`; the principal log picks
     this representative once `a₂ ≥ 2`.
   - The level-2 multiplier is `h₁'(0) = 1` exactly, so `ĥ = R̃_g + 1/α(g) − β = R̃_g + a₂` in the
     lift. This means `π ∘ ĥ^j = π ∘ R̃_g^j`.
   - Both levels are in `𝓕₁`, so remark (4.3.1) (the other sign) is **not needed**.
6. **Maximal domains.** `ParabData.Dφ` is Shishikura's maximal domain, pinned by `Q_sub`,
   `exhaust`, `left_inv` and `succ_iff`.
   - `φ w ∉ D₀` is allowed: the last point of an orbit need not be in `Dom f₀`. Step 1 needs this,
     because `φ₀(w̃₀) = 0` and `π(w̃₀) ∉ Dom g₀`.
   - For the same reason, `invOrbit` asks `z j ∈ D₀` only for `j ≥ 1`, and `PertData.orbit`
     concludes `f^[i](φ w) ∈ Df` only for `i < n`.
-/

namespace Work.Horn

open MandelDim
open _root_.MandelDim

/-! ## Status (2026-09-28, see `Submission/Work/Horn/NOTES_HORN.md`)

The assembly is done in `Submission/Work/Horn/hornOfParts.lean` (`Work.Horn.horn_of_parts`), which
builds `HornStatement` from

* `HornTopoStatement` (`Work.Horn.Topo.horn_topo`), `HornSCStatement` (`Work.Horn.SC.horn_sc`)
  — the lead's pieces in `Interfaces/HornParts.lean`;
* `Work.Horn.crit_of_parts`, `Work.Horn.cov_of_parts`, `Work.Horn.surj_inf_of_parts`
  (delegated: the assembly of `crit`, `cov_u/l`, `surj_u/l`, `inf_u/l` from `HornPhi`/`HornVarphi`);
* Lemma 5.4 (`g_second`, `g_F0`), `IsTInvariant d.DE` (or a `crit_orbit` lemma that avoids it)
  and `cl_im_pos`.

Once those exist, this theorem is literally
`Work.Horn.horn_of_parts Horn.Topo.horn_topo Horn.SC.horn_sc …`. -/

theorem horn : HornStatement := by
  -- The only inputs of `Work.Horn.horn_of_parts` that are not already available are the two
  -- conjuncts of Shishikura's Lemma 5.4 for the pushed-down horn map `g = pushdown d.E`:
  -- `g''(0) ≠ 0` (`HornData.g_second`) and `𝓕₀`-membership of the rescaled `g` (`HornData.g_F0`).
  -- `Work.Horn.horn_germ_F0` proves Lemma 5.4 unconditionally, using the `ParabData.horn_basin`
  -- field (Prop. 5.3's branched-covering structure of the horn map, supplied by §4.1/A.3).
  have hsecond : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀),
      MandelDim.IsF0Setup f₀ D₀ B c → deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 := by
    intro f₀ D₀ B c d hsetup
    have hF0 : MandelDim.InF0 f₀ D₀ :=
      ⟨hsetup.1, B, hsetup.2.1, c, ⟨hsetup.2.2.1, hsetup.2.2.2.1⟩,
        fun c' hc' => hsetup.2.2.2.2 c' hc'.1 hc'.2⟩
    have hBu : MandelDim.BuOf d B
        = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (d.η₀ + 1)) := by
      rw [MandelDim.BuOf, MandelDim.Btil]
      congr 1
      ext w
      simp [Set.mem_inter_iff, and_comm]
    have hBl : MandelDim.BlOf d B
        = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (d.η₀ + 1))) := by
      rw [MandelDim.BlOf, MandelDim.Btil]
      congr 1
      ext w
      simp [Set.mem_inter_iff, and_comm]
    obtain ⟨-, -, -, -, hup, hlo, hsub⟩ := HornTopo.horn_topo f₀ D₀ B c d hsetup
    exact (horn_germ_F0 f₀ D₀ hF0 d B hsetup.2.1 d.η₀ (MandelDim.BuOf d B) (MandelDim.BlOf d B)
      hBu hBl hsub hup hlo).1
  have hgF0 : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀),
      MandelDim.IsF0Setup f₀ D₀ B c →
      MandelDim.InF0
        (fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) *
          MandelDim.pushdown d.E (ζ / (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2)))
        ((fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) * ζ) ''
          insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))) := by
    intro f₀ D₀ B c d hsetup
    have hF0 : MandelDim.InF0 f₀ D₀ :=
      ⟨hsetup.1, B, hsetup.2.1, c, ⟨hsetup.2.2.1, hsetup.2.2.2.1⟩,
        fun c' hc' => hsetup.2.2.2.2 c' hc'.1 hc'.2⟩
    have hBu : MandelDim.BuOf d B
        = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (d.η₀ + 1)) := by
      rw [MandelDim.BuOf, MandelDim.Btil]
      congr 1
      ext w
      simp [Set.mem_inter_iff, and_comm]
    have hBl : MandelDim.BlOf d B
        = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (d.η₀ + 1))) := by
      rw [MandelDim.BlOf, MandelDim.Btil]
      congr 1
      ext w
      simp [Set.mem_inter_iff, and_comm]
    obtain ⟨-, -, -, -, hup, hlo, hsub⟩ := HornTopo.horn_topo f₀ D₀ B c d hsetup
    exact (horn_germ_F0 f₀ D₀ hF0 d B hsetup.2.1 d.η₀ (MandelDim.BuOf d B) (MandelDim.BlOf d B)
      hBu hBl hsub hup hlo).2
  -- The six Prop.-5.3 pieces of `Interfaces/HornParts.lean` are available from their areas.
  have hSC : MandelDim.HornSCStatement :=
    HornSC.horn_sc HornTopo.horn_topo BasinSC.basin_sc PlanarSC.planar_inter_sc
  have hcov := cov_from_parts HornTopo.horn_topo HornPhi.horn_phi HornVarphi.horn_varphi hSC
  have hinf := inf_from_parts HornTopo.horn_topo HornPhi.horn_phi HornVarphi.horn_varphi hSC
  exact horn_of_parts HornTopo.horn_topo hSC
    (crit_from_parts HornPhi.horn_phi HornVarphi.horn_varphi)
    hcov
    (surj_from_parts HornTopo.horn_topo HornPhi.horn_phi HornVarphi.horn_varphi hSC)
    hinf
    hsecond hgF0
    (hcl_of_parts HornTopo.horn_topo hSC hcov hinf)

end Work.Horn
